/* SPDX-License-Identifier: Apache-2.0
 * The fuzz target's plugin for OSS Verify's driver (their recipe's src/cli.c and
 * src/ossfuzz_adapter.h, fetched by fetch.sh): an OSS-Fuzz harness's plugin.c in
 * that recipe is these two lines, its name and the adapter. reac-pw is not among
 * the recipe's targets (release v2026.10.0-src), so this one is written here the
 * same way; the name is ours. */
#define OFT_TARGET_NAME "reac-pw-fuzz_qdisc"
#include "ossfuzz_adapter.h"
