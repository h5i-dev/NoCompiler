/* SPDX-License-Identifier: Apache-2.0
 * Shim for libreac's <reac/transport/reac_etf_qdisc.h>: the qdisc's delta (300000 ns,
 * as libreac 1.10.0 states it; the harness's ETF_DELTA_US cites it), the enum value the
 * harness's stand-ins return, and the prototypes they define. Not libreac's text. */
#ifndef NOCOMPILER_SHIM_REAC_ETF_QDISC_H
#define NOCOMPILER_SHIM_REAC_ETF_QDISC_H
#include <stddef.h>
#include <stdint.h>
#define REAC_ETF_QDISC_DELTA_NS 300000u
enum reac_etf_qdisc_state { REAC_ETF_QDISC_UNREADABLE = -1 };
enum reac_etf_qdisc_state reac_etf_qdisc_state(int ifindex, char *root_kind, size_t cap);
int reac_etf_qdisc_install(int ifindex, uint32_t delta_ns);
int reac_etf_qdisc_remove(int ifindex);
const char *reac_etf_qdisc_fix(int err);
#endif
