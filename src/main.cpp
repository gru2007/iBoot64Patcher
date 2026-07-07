//
//  main.cpp
//  src
//
//  Created by tihmstar on 27.09.19.
//  Copyright © 2019 tihmstar. All rights reserved.
//

#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <libpatchfinder/machopatchfinder32.hpp>
#include <libpatchfinder/machopatchfinder64.hpp>
#include <libpatchfinder/ibootpatchfinder/ibootpatchfinder32.hpp>
#include <libpatchfinder/ibootpatchfinder/ibootpatchfinder64.hpp>
#include <libpatchfinder/kernelpatchfinder/kernelpatchfinder32.hpp>
#include <libpatchfinder/kernelpatchfinder/kernelpatchfinder64.hpp>

#define HAS_ARG(x,y) (!strcmp(argv[i], x) && (i + y) < argc)

#define addpatch(pp) do {\
    auto p = pp; \
    patches.insert(patches.end(), p.begin(), p.end()); \
} while (0)

#define addloc(pp) do {\
    patches.push_back({pp,NULL,0}); \
} while (0)

using namespace tihmstar::patchfinder;

#define FLAG_UNLOCK_NVRAM (1 << 0)
#define FLAG_EXTRA_PATCHES (1 << 1)

static int extra_version = 0;
static uint64_t extra_base = 0;
static bool extra_paced = false;

#define extra_bswap32(x) __builtin_bswap32(x)
#define extra_hex_set(vers, hex1, hex2) (((vers) > extra_version) ? (hex1) : (hex2))

static uint32_t extra_load32(const void *p) {
    uint32_t v = 0;
    memcpy(&v, p, sizeof(v));
    return v;
}

static uint64_t extra_load64(const void *p) {
    uint64_t v = 0;
    memcpy(&v, p, sizeof(v));
    return v;
}

static void extra_store32(void *p, uint32_t v) {
    memcpy(p, &v, sizeof(v));
}

static void *extra_memmem(const void *haystack, size_t haystacklen, const void *needle, size_t needlelen) {
    if (!haystack || !needle || !needlelen) return (void *)haystack;
    if (needlelen > haystacklen) return nullptr;

    const uint8_t *h = (const uint8_t *)haystack;
    const uint8_t *n = (const uint8_t *)needle;
    for (size_t i = 0; i <= haystacklen - needlelen; i++) {
        if (h[i] == n[0] && !memcmp(h + i, n, needlelen)) {
            return (void *)(h + i);
        }
    }
    return nullptr;
}

static uint64_t extra_bof64(uint8_t *buf, uint64_t start, uint64_t where) {
    while (where >= start && where >= 4) {
        uint32_t op = extra_load32(buf + where);

        if ((op & 0xffc003ff) == 0x910003fd) {
            unsigned delta = (op >> 10) & 0xFFF;

            if ((delta & 0xf) == 0) {
                uint64_t prev = where - ((delta >> 0x4) + 1) * 0x4;
                uint32_t au = extra_load32(buf + prev);

                if ((au & 0xffc003e0) == 0xa98003e0) return prev;

                while (where > start && where >= 4) {
                    where -= 0x4;
                    au = extra_load32(buf + where);

                    if (((au & 0xffc003ff) == 0xd10003ff) && (((au >> 0xA) & 0xfff) == delta + 0x10)) return where;

                    if ((au & 0xffc003e0) != 0xa90003e0) {
                        where += 0x4;
                        break;
                    }
                }
            }
        }

        where -= 0x4;
    }

    return 0;
}

static uint64_t extra_xref64(const uint8_t *ibot, uint64_t start, uint64_t end, uint64_t what) {
    uint64_t value[32];
    memset(value, 0x0, sizeof(value));

    end &= ~0x3;

    for (uint64_t i = start & ~0x3; i < end; i += 0x4) {
        uint32_t op = extra_load32(ibot + i);
        unsigned reg = op & 0x1f;

        if ((op & 0x9f000000) == 0x90000000) {
            signed adr = ((op & 0x60000000) >> 0x12) | ((op & 0xffffe0) << 8);
            value[reg] = ((long long)adr << 1) + (i & ~0xfff);
        } else if ((op & 0xff000000) == 0x91000000) {
            unsigned rn = (op >> 0x5) & 0x1f;

            if (rn == 0x1f) {
                value[reg] = 0;
                continue;
            }

            unsigned shift = (op >> 0x16) & 0x3;
            unsigned imm = (op >> 0xA) & 0xfff;

            if (shift == 1) {
                imm <<= 0xC;
            } else if (shift > 1) {
                continue;
            }

            value[reg] = value[rn] + imm;
        } else if ((op & 0xf9C00000) == 0xf9400000) {
            unsigned rn = (op >> 0x5) & 0x1f;
            unsigned imm = ((op >> 0xA) & 0xfff) << 0x3;

            if (!imm) continue;

            value[reg] = value[rn] + imm;
        } else if ((op & 0x9f000000) == 0x10000000) {
            signed adr = ((op & 0x60000000) >> 0x12) | ((op & 0xffffe0) << 8);
            value[reg] = ((long long)adr >> 0xB) + i;
        } else if ((op & 0xff000000) == 0x58000000) {
            unsigned adr = (op & 0xffffe0) >> 3;
            value[reg] = adr + i;
        } else if ((op & 0xfc000000) == 0x94000000) {
            signed imm = (op & 0x3ffffff) << 2;
            if (op & 0x2000000) imm |= 0xf << 0x1c;

            unsigned adr = (unsigned)(i + imm);
            if (adr == what) return i;
        }

        if (value[reg] == what && reg != 0x1f) return i;
    }

    return 0;
}

static uint64_t extra_insn_is_bl(uint8_t *ibot, size_t length, uint64_t xref, int bl_to_count, int add) {
    for (int i = 0; i < bl_to_count; i++) {
        do {
            if (add < 0 && xref < (uint64_t)(-add)) return 0;
            xref += add;
            if (xref + 4 > length) return 0;
        } while ((extra_load32(ibot + xref) >> 0x1a) != 0x25);
    }

    return xref;
}

static uint64_t extra_find_any_insn(uint8_t *ibot, size_t length, uint64_t xref, int x, int add, uint32_t mask, uint32_t value) {
    for (int i = 0; i < x; i++) {
        do {
            if (add < 0 && xref < (uint64_t)(-add)) return 0;
            xref += add;
            if (xref + 4 > length) return 0;
        } while ((extra_load32(ibot + xref) & mask) != value);
    }

    return xref;
}

static uint8_t *extra_memdata(uint8_t *ibot, uint32_t data, int data_size, uint8_t *last_ptr, size_t length) {
    if (last_ptr < ibot || last_ptr >= ibot + length) return nullptr;

    size_t loc = length - (size_t)(last_ptr - ibot);
    if (loc <= 4) return nullptr;

    return (uint8_t *)extra_memmem(last_ptr + 0x4, loc - 0x4, (const char *)&data, data_size);
}

static bool extra_detect_pac(uint8_t *ibot, size_t length) {
    uint8_t *pac_search = extra_memdata(ibot, extra_bswap32(0x7f2303d5), 0x4, ibot, length);
    extra_paced = pac_search != nullptr;
    return extra_paced;
}

static int extra_allow_any_imagetype(uint8_t *ibot, size_t length) {
    uint64_t xref = 0;
    uint8_t *where = nullptr;
    uint32_t search = 0, opcode = 0;
    int rd = extra_hex_set(3406, 0x5, 0x4);
    const char *str = ((extra_version > 3406) ? "cebilefciladrmmhtreptlhptmbr" : "cebilefctmbrtlhptreprmmh");

    printf("\n[%s]: allowing to load any type of images...\n", __func__);

    where = (uint8_t *)extra_memmem(ibot, length, str, strlen(str));
    if (!where) return -1;

    xref = extra_xref64(ibot, 0x0, length, (uint64_t)(where - ibot));
    if (!xref) return -1;

    opcode = (0x6 << 29) | (0x25 << 23) | rd;
    extra_store32(ibot + xref, extra_bswap32(opcode));

    printf("[%s]: patched to MOVZ x%d, #0 insn = 0x%llx\n", __func__, rd, extra_base + xref);

    search = extra_hex_set(5540, extra_hex_set(3406, 0xe5071f32, 0xe60b0032), 0xe6008052);
    where = extra_memdata(ibot, extra_bswap32(search), 0x4, ibot, length);
    if (!where) return -1;

    rd = extra_hex_set(3406, 0x6, 0x5);
    opcode = (0x2 << 29) | (0x25 << 23) | rd;
    extra_store32(where, extra_bswap32(opcode));

    printf("[%s]: patched to MOVZ w%d, #0 insn = 0x%llx\n", __func__, rd, extra_base + (uint64_t)(where - ibot));
    printf("[%s]: successfully allowed to load any image types!\n", __func__);

    return 0;
}

static int extra_prevent_kaslr_slide(uint8_t *ibot, size_t length) {
    uint64_t where = 0;
    uint32_t opcode = 0;
    uint8_t *current = nullptr;
    unsigned _rd = 0, rd = 0;

    if ((extra_version < 3406) || (extra_version > 4513)) return 0;

    printf("\n[%s]: patching the kaslr slide...\n", __func__);

    current = (uint8_t *)extra_memmem(ibot, length, "__PAGEZERO", sizeof("__PAGEZERO"));
    if (!current) return -1;

    where = extra_xref64(ibot, 0x0, length, (uint64_t)(current - ibot));
    if (!where) return -1;

    printf("[%s]: found the 'load_kernelcache()' function!\n", __func__);

    if (extra_version == 4513) {
        where = extra_find_any_insn(ibot, length, where, 2, -0x4, 0x3a000000, 0x28000000);
        if (!where) return -1;
        where += 0x14;
    } else {
        where = extra_insn_is_bl(ibot, length, where, 0x3, -0x4);
        if (!where) return -1;
    }

    for (int i = 0x4; i != (extra_version == 4513 ? 0x40 : 0x24); i += 0x4) {
        if (i == 0x8) {
            _rd = extra_load32(ibot + where + i) & 0x1f;
            opcode = ((0x6 << 29) | (0x25 << 23) | (0x0 << 5) | _rd);
            extra_store32(ibot + where + i, opcode);

            printf("[%s]: patched 'slide_phys' to MOV x%u, #0 = 0x%llx\n", __func__, _rd, extra_base + where + i);
        } else if (i == (extra_version == 4513 ? 0x28 : 0x18)) {
            rd = extra_load32(ibot + where + i) & 0x1f;
            opcode = ((0x5 << 29) | (0x50 << 21) | ((_rd & 0x1f) << 16) | ((-1 & 0x1f) << 5) | rd);
            extra_store32(ibot + where + i, opcode);

            printf("[%s]: patched 'slide_virt' to MOV x%u, x%u = 0x%llx\n", __func__, rd, _rd, extra_base + where + i);
        } else {
            extra_store32(ibot + where + i, extra_bswap32(0x1f2003d5));
        }
    }

    printf("[%s]: NOPed all other instructions.\n"
           "[%s]: successfully patched the kaslr slide!\n",
           __func__, __func__);

    return 0;
}

static int apply_extra_patches(uint8_t *ibot, size_t length) {
    if (length < 0x320) return -1;

    extra_version = atoi((const char *)(ibot + 0x286));
    extra_base = extra_load64(ibot + extra_hex_set(6603, 0x318, 0x300));

    printf("[%s]: detected iBoot-%d!\n", __func__, extra_version);
    printf("[%s]: base_addr = 0x%llx\n", __func__, extra_base);

    extra_detect_pac(ibot, length);

    if (!extra_memmem(ibot, length, "__PAGEZERO", strlen("__PAGEZERO"))) {
        printf("[%s]: no kernel load routine, skipping -e patches.\n", __func__);
        return 0;
    }

    if (extra_allow_any_imagetype(ibot, length) != 0) {
        printf("[%s]: unable to allow loading any image types.\n", __func__);
        return -1;
    }

    if (extra_prevent_kaslr_slide(ibot, length) != 0) {
        printf("[%s]: unable to patch the kaslr slide.\n", __func__);
        return -1;
    }

    return 0;
}

int main(int argc, const char * argv[]) {
    FILE* fp = nullptr;
    FILE* fp2 = nullptr;
    char* cmd_handler_str = nullptr;
    char* custom_boot_args = nullptr;
    uint64_t cmd_handler_ptr = 0;
    int flags = 0;

    printf("Version: " VERSION_COMMIT_SHA "-" VERSION_COMMIT_COUNT "\n");
    
    if(argc < 3) {
        printf("Usage: %s <iboot_in> <iboot_out> [args]\n", argv[0]);
        printf("\t-b <str>\tApply custom boot args.\n");
        printf("\t-c <cmd> <ptr>\tChange a command handler's pointer (hex).\n");
        printf("\t-n \t\tApply unlock nvram patch.\n");
        printf("\t-e \t\tApply extra patches: allow any image type + prevent KASLR slide where supported.\n");
        return -1;
    }
    
    printf("%s: Starting...\n", __FUNCTION__);
    
    for(int i = 0; i < argc; i++) {
        if(HAS_ARG("-b", 1)) {
            custom_boot_args = (char*) argv[i+1];
        } else if(HAS_ARG("-n", 0)) {
            flags |= FLAG_UNLOCK_NVRAM;
        } else if(HAS_ARG("-e", 0)) {
            flags |= FLAG_EXTRA_PATCHES;
        }else if(HAS_ARG("-c", 2)) {
            cmd_handler_str = (char*) argv[i+1];
            sscanf((char*) argv[i+2], "0x%016llX", &cmd_handler_ptr);
        }
    }
    
    std::vector<patch> patches;
    
    ibootpatchfinder *ibpf = nullptr;
    kernelpatchfinder *kpf = nullptr;
    cleanup([&]{
      safeDelete(ibpf);
      safeDelete(kpf);
    });
    const char *iboot_path = argv[1];
    const char *iboot_patched_path = argv[2];
    struct stat st{0};
    if(stat(iboot_path, &st) < 0) {
      printf("%s: Error getting iBoot size for %s!\n", __FUNCTION__, iboot_path);
      return -1;
    }
    size_t iboot_size = st.st_size;
    try {
      kpf = kernelpatchfinder64::make_kernelpatchfinder64(iboot_path);
    } catch (...) {
      try {
        kpf = kernelpatchfinder32::make_kernelpatchfinder32(iboot_path);
      } catch (...) {
        try {
          ibpf = ibootpatchfinder64::make_ibootpatchfinder64(iboot_path);
        } catch (...) {
          ibpf = ibootpatchfinder32::make_ibootpatchfinder32(iboot_path);
        }
      }
    }
    /* Check to see if the loader has a kernel load routine before trying to apply custom boot args + debug-enabled override. */
    if(ibpf->has_kernel_load()) {
        if(custom_boot_args) {
            try {
                printf("getting get_boot_arg_patch(%s) patch\n",custom_boot_args);
                addpatch(ibpf->get_boot_arg_patch(custom_boot_args));
            } catch (tihmstar::exception &e) {
                printf("%s: Error doing patch_boot_args()! (%s)\n", __FUNCTION__, e.what());
                return -1;
            }
        }
        
        
        /* Only bootloaders with the kernel load routines pass the DeviceTree. */
        try {
            printf("getting get_debug_enabled_patch() patch\n");
            addpatch(ibpf->get_debug_enabled_patch());
        } catch (tihmstar::exception &e) {
            printf("%s: Error doing patch_debug_enabled()! (%s)\n", __FUNCTION__, e.what());
            return -1;
        }
    }
    
    /* Ensure that the loader has a shell. */
    if(ibpf->has_recovery_console()) {
        if (cmd_handler_str && cmd_handler_ptr) {
            try {
                printf("getting get_cmd_handler_patch(%s,0x%016llx) patch\n",cmd_handler_str,cmd_handler_ptr);
                addpatch(ibpf->get_cmd_handler_patch(cmd_handler_str, cmd_handler_ptr));
            } catch (tihmstar::exception &e) {
                printf("%s: Error doing patch_cmd_handler()! (%s)\n", __FUNCTION__, e.what());
                return -1;
            }
        }
        
        if (flags & FLAG_UNLOCK_NVRAM) {
            try {
                printf("getting get_unlock_nvram_patch() patch\n");
                addpatch(ibpf->get_unlock_nvram_patch());
            } catch (tihmstar::exception &e) {
                printf("%s: Error doing get_unlock_nvram_patch()! (%s)\n", __FUNCTION__, e.what());
                return -1;
            }
            try {
                printf("getting get_freshnonce_patch() patch\n");
                addpatch(ibpf->get_freshnonce_patch());
            } catch (tihmstar::exception &e) {
                printf("%s: Error doing get_freshnonce_patch()! (%s)\n", __FUNCTION__, e.what());
                return -1;
            }
        }
    }
    
    /* All loaders have the RSA check. */
    try {
        printf("getting get_sigcheck_patch() patch\n");
        addpatch(ibpf->get_sigcheck_patch());
    } catch (tihmstar::exception &e) {
        printf("%s: Error doing patch_rsa_check()! (%s)\n", __FUNCTION__, e.what());
        return -1;
    }
    
    
    /* Write out the patched file... */
    fp = fopen(iboot_patched_path, "wb+");
    if(!fp) {
        printf("%s: Unable to open %s!\n", __FUNCTION__, iboot_patched_path);
        return -1;
    }
    fp2 = fopen(iboot_path, "rb+");
    if(!fp2) {
        printf("%s: Unable to open %s!\n", __FUNCTION__, iboot_path);
        fflush(fp);
        fclose(fp);
        return -1;
    }
    char *deciboot = (char *)calloc(1, iboot_size);
    size_t ret = fread(deciboot, 1, iboot_size, fp2);
    if(ret != iboot_size) {
      printf("%s: Unable to read iBoot, read size %zu/%zu!\n", __FUNCTION__, ret, iboot_size);
      fflush(fp);
      fclose(fp);
      fflush(fp2);
      fclose(fp2);
      free(deciboot);
      return -1;
    }
    fflush(fp2);
    fclose(fp2);

    for (const auto& p2 : patches) {
      printf("%s: Applying patch=0x%016llx: ", __FUNCTION__, p2._location);
      for (int i=0; i<p2._patchSize; i++) {
        printf("%02x",((uint8_t*)p2._patch)[i]);
      }
      if (p2._patchSize == 4) {
        printf(" 0x%08x",*(uint32_t*)p2._patch);
      } else if (p2._patchSize == 2) {
        printf(" 0x%04x",*(uint16_t*)p2._patch);
      }
      printf("\n");
      auto off = (ibootpatchfinder::loc64_t)(p2._location - ibpf->find_base());
      memcpy(&deciboot[off], p2._patch, p2._patchSize);
    }

    if (flags & FLAG_EXTRA_PATCHES) {
      printf("%s: Applying -e extra patches...\n", __FUNCTION__);
      if (apply_extra_patches((uint8_t *)deciboot, iboot_size) != 0) {
        printf("%s: Error applying -e extra patches!\n", __FUNCTION__);
        fflush(fp);
        fclose(fp);
        free(deciboot);
        return -1;
      }
    }

    printf("%s: Writing out patched file to %s...\n", __FUNCTION__, iboot_patched_path);
    ret = fwrite(deciboot,1, iboot_size, fp);
    if(ret != iboot_size) {
      printf("%s: Unable to write patched iBoot, wrote size %zu/%zu!\n", __FUNCTION__, ret, iboot_size);
      fflush(fp);
      fclose(fp);
      fflush(fp2);
      fclose(fp2);
      free(deciboot);
      return -1;
    }

    fflush(fp);
    fclose(fp);
    free(deciboot);

    printf("%s: Quitting...\n", __FUNCTION__);
    
    return 0;
}
