/* SPDX-License-Identifier: Apache-2.0
 * Shim for reac-pw's src/reac_qdisc.h: only the declaration the harness uses.
 * Upstream's prototype (f86a30a3, src/reac_qdisc.h:129), restated. */
#ifndef NOCOMPILER_SHIM_REAC_QDISC_H
#define NOCOMPILER_SHIM_REAC_QDISC_H
int reac_qdisc_etf_catchup_slots(unsigned lead_us, int fps);
#endif
