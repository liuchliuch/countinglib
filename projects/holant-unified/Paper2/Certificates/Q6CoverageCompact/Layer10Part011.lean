import Paper2.Certificates.Q6CoverageCompact.Layer10Part010

namespace Paper2.Certificates.Q6.Coverage

def ntree10RLRLLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRLLLRRL i else ntree10RLRLLLRRR (i - 8)

def ntree10RLRLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RLRLLLRL i else ntree10RLRLLLRR (i - 16)

def ntree10RLRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RLRLLLL i else ntree10RLRLLLR (i - 31)

def ntree10RLRLLRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨747,by decide⟩,⟨2283,by decide⟩,⟨1715,by decide⟩] | 1 => ![⟨2657,by decide⟩,⟨2217,by decide⟩,⟨2658,by decide⟩] | 2 => ![⟨1242,by decide⟩,⟨2659,by decide⟩,⟨1749,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨1768,by decide⟩,⟨1768,by decide⟩] | 4 => ![⟨1242,by decide⟩,⟨2660,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨2661,by decide⟩,⟨2662,by decide⟩,⟨1180,by decide⟩] | _ => ![⟨2661,by decide⟩,⟨2663,by decide⟩,⟨2631,by decide⟩]

def ntree10RLRLLRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2664,by decide⟩,⟨2662,by decide⟩,⟨2553,by decide⟩] | 1 => ![⟨2664,by decide⟩,⟨2665,by decide⟩,⟨2616,by decide⟩] | 2 => ![⟨2585,by decide⟩,⟨2585,by decide⟩,⟨2666,by decide⟩] | 3 => ![⟨2667,by decide⟩,⟨2585,by decide⟩,⟨2585,by decide⟩] | 4 => ![⟨2667,by decide⟩,⟨2668,by decide⟩,⟨2666,by decide⟩] | 5 => ![⟨2613,by decide⟩,⟨15,by decide⟩,⟨144,by decide⟩] | 6 => ![⟨2553,by decide⟩,⟨2266,by decide⟩,⟨2669,by decide⟩] | _ => ![⟨2662,by decide⟩,⟨2670,by decide⟩,⟨109,by decide⟩]

def ntree10RLRLLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RLRLLRLLL i else ntree10RLRLLRLLR (i - 7)

def ntree10RLRLLRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2662,by decide⟩,⟨2663,by decide⟩,⟨1749,by decide⟩] | 1 => ![⟨2662,by decide⟩,⟨2671,by decide⟩,⟨2266,by decide⟩] | 2 => ![⟨2662,by decide⟩,⟨2665,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨2585,by decide⟩,⟨2672,by decide⟩,⟨2585,by decide⟩] | 4 => ![⟨2585,by decide⟩,⟨2668,by decide⟩,⟨2585,by decide⟩] | 5 => ![⟨2662,by decide⟩,⟨2662,by decide⟩,⟨1776,by decide⟩] | 6 => ![⟨2673,by decide⟩,⟨2673,by decide⟩,⟨1777,by decide⟩] | _ => ![⟨2664,by decide⟩,⟨2674,by decide⟩,⟨2675,by decide⟩]

def ntree10RLRLLRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2676,by decide⟩,⟨2677,by decide⟩,⟨2678,by decide⟩] | 1 => ![⟨2679,by decide⟩,⟨2285,by decide⟩,⟨2669,by decide⟩] | 2 => ![⟨2680,by decide⟩,⟨2680,by decide⟩,⟨1695,by decide⟩] | 3 => ![⟨2681,by decide⟩,⟨2681,by decide⟩,⟨1695,by decide⟩] | 4 => ![⟨2673,by decide⟩,⟨2673,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨2680,by decide⟩,⟨2682,by decide⟩,⟨1695,by decide⟩] | 6 => ![⟨2681,by decide⟩,⟨2683,by decide⟩,⟨2684,by decide⟩] | _ => ![⟨2673,by decide⟩,⟨2677,by decide⟩,⟨2685,by decide⟩]

def ntree10RLRLLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRLLRLRL i else ntree10RLRLLRLRR (i - 8)

def ntree10RLRLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RLRLLRLL i else ntree10RLRLLRLR (i - 15)

def ntree10RLRLLRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨752,by decide⟩,⟨752,by decide⟩,⟨2686,by decide⟩] | 1 => ![⟨2687,by decide⟩,⟨2299,by decide⟩,⟨2688,by decide⟩] | 2 => ![⟨2689,by decide⟩,⟨595,by decide⟩,⟨2690,by decide⟩] | 3 => ![⟨2691,by decide⟩,⟨13,by decide⟩,⟨2689,by decide⟩] | 4 => ![⟨2691,by decide⟩,⟨596,by decide⟩,⟨2690,by decide⟩] | 5 => ![⟨2692,by decide⟩,⟨2557,by decide⟩,⟨2690,by decide⟩] | 6 => ![⟨2691,by decide⟩,⟨1633,by decide⟩,⟨2693,by decide⟩] | _ => ![⟨1167,by decide⟩,⟨15,by decide⟩,⟨2607,by decide⟩]

def ntree10RLRLLRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1168,by decide⟩,⟨13,by decide⟩,⟨2607,by decide⟩] | 1 => ![⟨1242,by decide⟩,⟨2694,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨2695,by decide⟩,⟨1172,by decide⟩,⟨2696,by decide⟩] | 3 => ![⟨2695,by decide⟩,⟨9,by decide⟩,⟨2695,by decide⟩] | 4 => ![⟨2697,by decide⟩,⟨2564,by decide⟩,⟨2696,by decide⟩] | 5 => ![⟨2695,by decide⟩,⟨1619,by decide⟩,⟨2695,by decide⟩] | 6 => ![⟨2698,by decide⟩,⟨2203,by decide⟩,⟨2690,by decide⟩] | _ => ![⟨2699,by decide⟩,⟨768,by decide⟩,⟨2690,by decide⟩]

def ntree10RLRLLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRLLRRLL i else ntree10RLRLLRRLR (i - 8)

def ntree10RLRLLRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2689,by decide⟩,⟨159,by decide⟩,⟨2689,by decide⟩] | 1 => ![⟨2689,by decide⟩,⟨1626,by decide⟩,⟨2689,by decide⟩] | 2 => ![⟨2700,by decide⟩,⟨2321,by decide⟩,⟨1820,by decide⟩] | 3 => ![⟨1229,by decide⟩,⟨2701,by decide⟩,⟨1656,by decide⟩] | 4 => ![⟨11,by decide⟩,⟨2702,by decide⟩,⟨2639,by decide⟩] | 5 => ![⟨752,by decide⟩,⟨2703,by decide⟩,⟨2704,by decide⟩] | 6 => ![⟨2705,by decide⟩,⟨2574,by decide⟩,⟨1815,by decide⟩] | _ => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨2646,by decide⟩]

def ntree10RLRLLRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1194,by decide⟩,⟨2328,by decide⟩,⟨1711,by decide⟩] | 1 => ![⟨1242,by decide⟩,⟨2706,by decide⟩,⟨1663,by decide⟩] | 2 => ![⟨2707,by decide⟩,⟨15,by decide⟩,⟨2708,by decide⟩] | 3 => ![⟨2563,by decide⟩,⟨2563,by decide⟩,⟨1705,by decide⟩] | 4 => ![⟨9,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | 5 => ![⟨2709,by decide⟩,⟨2577,by decide⟩,⟨2708,by decide⟩] | 6 => ![⟨2202,by decide⟩,⟨2202,by decide⟩,⟨1711,by decide⟩] | _ => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩]

def ntree10RLRLLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRLLRRRL i else ntree10RLRLLRRRR (i - 8)

def ntree10RLRLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RLRLLRRL i else ntree10RLRLLRRR (i - 16)

def ntree10RLRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RLRLLRL i else ntree10RLRLLRR (i - 31)

def ntree10RLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10RLRLLL i else ntree10RLRLLR (i - 63)

def ntree10RLRLRLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨794,by decide⟩,⟨794,by decide⟩,⟨2710,by decide⟩] | 1 => ![⟨2711,by decide⟩,⟨2341,by decide⟩,⟨2712,by decide⟩] | 2 => ![⟨1324,by decide⟩,⟨2713,by decide⟩,⟨2714,by decide⟩] | 3 => ![⟨2715,by decide⟩,⟨2586,by decide⟩,⟨2716,by decide⟩] | 4 => ![⟨2717,by decide⟩,⟨2587,by decide⟩,⟨2715,by decide⟩] | 5 => ![⟨2717,by decide⟩,⟨2588,by decide⟩,⟨2716,by decide⟩] | _ => ![⟨2689,by decide⟩,⟨15,by decide⟩,⟨2718,by decide⟩]

def ntree10RLRLRLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2719,by decide⟩,⟨595,by decide⟩,⟨2720,by decide⟩] | 1 => ![⟨2721,by decide⟩,⟨2596,by decide⟩,⟨2718,by decide⟩] | 2 => ![⟨2722,by decide⟩,⟨2598,by decide⟩,⟨2720,by decide⟩] | 3 => ![⟨2723,by decide⟩,⟨747,by decide⟩,⟨2689,by decide⟩] | 4 => ![⟨2724,by decide⟩,⟨2724,by decide⟩,⟨2355,by decide⟩] | 5 => ![⟨2725,by decide⟩,⟨2725,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨2724,by decide⟩,⟨2726,by decide⟩,⟨2727,by decide⟩] | _ => ![⟨2725,by decide⟩,⟨2728,by decide⟩,⟨1332,by decide⟩]

def ntree10RLRLRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RLRLRLLLL i else ntree10RLRLRLLLR (i - 7)

def ntree10RLRLRLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨1626,by decide⟩,⟨1361,by decide⟩] | 1 => ![⟨2729,by decide⟩,⟨2357,by decide⟩,⟨2729,by decide⟩] | 2 => ![⟨2730,by decide⟩,⟨2185,by decide⟩,⟨2731,by decide⟩] | 3 => ![⟨2725,by decide⟩,⟨2732,by decide⟩,⟨2186,by decide⟩] | 4 => ![⟨2733,by decide⟩,⟨2355,by decide⟩,⟨2733,by decide⟩] | 5 => ![⟨2733,by decide⟩,⟨2727,by decide⟩,⟨2734,by decide⟩] | 6 => ![⟨2553,by decide⟩,⟨1332,by decide⟩,⟨2735,by decide⟩] | _ => ![⟨2736,by decide⟩,⟨2365,by decide⟩,⟨2736,by decide⟩]

def ntree10RLRLRLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1860,by decide⟩,⟨2197,by decide⟩,⟨2737,by decide⟩] | 1 => ![⟨2365,by decide⟩,⟨2738,by decide⟩,⟨2738,by decide⟩] | 2 => ![⟨1637,by decide⟩,⟨2739,by decide⟩,⟨2739,by decide⟩] | 3 => ![⟨2733,by decide⟩,⟨2357,by decide⟩,⟨2733,by decide⟩] | 4 => ![⟨2740,by decide⟩,⟨2203,by decide⟩,⟨1340,by decide⟩] | 5 => ![⟨2736,by decide⟩,⟨2369,by decide⟩,⟨2736,by decide⟩] | 6 => ![⟨2741,by decide⟩,⟨2207,by decide⟩,⟨2737,by decide⟩] | _ => ![⟨2742,by decide⟩,⟨2355,by decide⟩,⟨2742,by decide⟩]

def ntree10RLRLRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRLRLLRL i else ntree10RLRLRLLRR (i - 8)

def ntree10RLRLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RLRLRLLL i else ntree10RLRLRLLR (i - 15)

def ntree10RLRLRLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2743,by decide⟩,⟨2724,by decide⟩,⟨2742,by decide⟩] | 1 => ![⟨2744,by decide⟩,⟨2725,by decide⟩,⟨1180,by decide⟩] | 2 => ![⟨2355,by decide⟩,⟨2745,by decide⟩,⟨2745,by decide⟩] | 3 => ![⟨2725,by decide⟩,⟨2746,by decide⟩,⟨1663,by decide⟩] | 4 => ![⟨2747,by decide⟩,⟨1663,by decide⟩,⟨2748,by decide⟩] | 5 => ![⟨2749,by decide⟩,⟨180,by decide⟩,⟨2747,by decide⟩] | 6 => ![⟨2750,by decide⟩,⟨1663,by decide⟩,⟨1663,by decide⟩] | _ => ![⟨2751,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩]

def ntree10RLRLRLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2752,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨1877,by decide⟩,⟨845,by decide⟩,⟨1877,by decide⟩] | 2 => ![⟨2753,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨2754,by decide⟩,⟨580,by decide⟩,⟨1877,by decide⟩] | 4 => ![⟨580,by decide⟩,⟨2755,by decide⟩,⟨1663,by decide⟩] | 5 => ![⟨248,by decide⟩,⟨1663,by decide⟩,⟨2756,by decide⟩] | 6 => ![⟨2747,by decide⟩,⟨15,by decide⟩,⟨2747,by decide⟩] | _ => ![⟨1637,by decide⟩,⟨1637,by decide⟩,⟨2757,by decide⟩]

def ntree10RLRLRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRLRLRLL i else ntree10RLRLRLRLR (i - 8)

def ntree10RLRLRLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2365,by decide⟩,⟨2758,by decide⟩,⟨2758,by decide⟩] | 1 => ![⟨2202,by decide⟩,⟨2202,by decide⟩,⟨1361,by decide⟩] | 2 => ![⟨2759,by decide⟩,⟨2202,by decide⟩,⟨248,by decide⟩] | 3 => ![⟨2760,by decide⟩,⟨2365,by decide⟩,⟨2365,by decide⟩] | 4 => ![⟨2761,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 5 => ![⟨1886,by decide⟩,⟨2377,by decide⟩,⟨1886,by decide⟩] | 6 => ![⟨2206,by decide⟩,⟨2206,by decide⟩,⟨2757,by decide⟩] | _ => ![⟨2762,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩]

def ntree10RLRLRLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2763,by decide⟩,⟨2206,by decide⟩,⟨1886,by decide⟩] | 1 => ![⟨2355,by decide⟩,⟨2764,by decide⟩,⟨2745,by decide⟩] | 2 => ![⟨2747,by decide⟩,⟨1681,by decide⟩,⟨2748,by decide⟩] | 3 => ![⟨2747,by decide⟩,⟨1626,by decide⟩,⟨2747,by decide⟩] | 4 => ![⟨2742,by decide⟩,⟨2367,by decide⟩,⟨2765,by decide⟩] | 5 => ![⟨2733,by decide⟩,⟨2745,by decide⟩,⟨2766,by decide⟩] | 6 => ![⟨2767,by decide⟩,⟨2586,by decide⟩,⟨2768,by decide⟩] | _ => ![⟨2767,by decide⟩,⟨2585,by decide⟩,⟨2767,by decide⟩]

def ntree10RLRLRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRLRLRRL i else ntree10RLRLRLRRR (i - 8)

def ntree10RLRLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RLRLRLRL i else ntree10RLRLRLRR (i - 16)

def ntree10RLRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RLRLRLL i else ntree10RLRLRLR (i - 31)

def ntree10RLRLRRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2769,by decide⟩,⟨15,by decide⟩,⟨2769,by decide⟩] | 1 => ![⟨191,by decide⟩,⟨15,by decide⟩,⟨2770,by decide⟩] | 2 => ![⟨1877,by decide⟩,⟨595,by decide⟩,⟨2771,by decide⟩] | 3 => ![⟨2355,by decide⟩,⟨2772,by decide⟩,⟨2772,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨2773,by decide⟩,⟨2773,by decide⟩] | 5 => ![⟨2585,by decide⟩,⟨2593,by decide⟩,⟨2593,by decide⟩] | _ => ![⟨2774,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩]

def ntree10RLRLRRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2775,by decide⟩,⟨595,by decide⟩,⟨595,by decide⟩] | 1 => ![⟨2769,by decide⟩,⟨2386,by decide⟩,⟨2769,by decide⟩] | 2 => ![⟨2776,by decide⟩,⟨2224,by decide⟩,⟨2770,by decide⟩] | 3 => ![⟨2777,by decide⟩,⟨2203,by decide⟩,⟨2771,by decide⟩] | 4 => ![⟨2355,by decide⟩,⟨2355,by decide⟩,⟨2778,by decide⟩] | 5 => ![⟨2355,by decide⟩,⟨2779,by decide⟩,⟨2779,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨1401,by decide⟩,⟨2780,by decide⟩] | _ => ![⟨2781,by decide⟩,⟨2357,by decide⟩,⟨2778,by decide⟩]

def ntree10RLRLRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RLRLRRLLL i else ntree10RLRLRRLLR (i - 7)

def ntree10RLRLRRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨2782,by decide⟩,⟨1401,by decide⟩] | 1 => ![⟨1708,by decide⟩,⟨2782,by decide⟩,⟨2780,by decide⟩] | 2 => ![⟨2392,by decide⟩,⟨2392,by decide⟩,⟨2778,by decide⟩] | 3 => ![⟨2783,by decide⟩,⟨2395,by decide⟩,⟨2784,by decide⟩] | 4 => ![⟨685,by decide⟩,⟨2785,by decide⟩,⟨1401,by decide⟩] | 5 => ![⟨2733,by decide⟩,⟨2355,by decide⟩,⟨2786,by decide⟩] | 6 => ![⟨191,by decide⟩,⟨1401,by decide⟩,⟨2787,by decide⟩] | _ => ![⟨2365,by decide⟩,⟨2365,by decide⟩,⟨2788,by decide⟩]

def ntree10RLRLRRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2736,by decide⟩,⟨2365,by decide⟩,⟨2789,by decide⟩] | 1 => ![⟨2365,by decide⟩,⟨2790,by decide⟩,⟨2790,by decide⟩] | 2 => ![⟨1637,by decide⟩,⟨2791,by decide⟩,⟨2791,by decide⟩] | 3 => ![⟨2398,by decide⟩,⟨2398,by decide⟩,⟨2778,by decide⟩] | 4 => ![⟨2792,by decide⟩,⟨2401,by decide⟩,⟨2786,by decide⟩] | 5 => ![⟨2402,by decide⟩,⟨2402,by decide⟩,⟨2788,by decide⟩] | 6 => ![⟨2793,by decide⟩,⟨2403,by decide⟩,⟨2789,by decide⟩] | _ => ![⟨2742,by decide⟩,⟨2794,by decide⟩,⟨2795,by decide⟩]

def ntree10RLRLRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRLRRLRL i else ntree10RLRLRRLRR (i - 8)

def ntree10RLRLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RLRLRRLL i else ntree10RLRLRRLR (i - 15)

def ntree10RLRLRRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨845,by decide⟩,⟨1711,by decide⟩] | 1 => ![⟨2747,by decide⟩,⟨1429,by decide⟩,⟨2796,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨1711,by decide⟩] | 3 => ![⟨2797,by decide⟩,⟨896,by decide⟩,⟨1942,by decide⟩] | 4 => ![⟨2392,by decide⟩,⟨2798,by decide⟩,⟨2794,by decide⟩] | 5 => ![⟨1917,by decide⟩,⟨2799,by decide⟩,⟨1429,by decide⟩] | 6 => ![⟨2747,by decide⟩,⟨1948,by decide⟩,⟨2800,by decide⟩] | _ => ![⟨2365,by decide⟩,⟨2801,by decide⟩,⟨2801,by decide⟩]

def ntree10RLRLRRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1637,by decide⟩,⟨2802,by decide⟩,⟨2802,by decide⟩] | 1 => ![⟨2803,by decide⟩,⟨2418,by decide⟩,⟨1959,by decide⟩] | 2 => ![⟨2804,by decide⟩,⟨2419,by decide⟩,⟨1955,by decide⟩] | 3 => ![⟨2805,by decide⟩,⟨2806,by decide⟩,⟨2796,by decide⟩] | 4 => ![⟨2355,by decide⟩,⟨2794,by decide⟩,⟨2794,by decide⟩] | 5 => ![⟨1964,by decide⟩,⟨1968,by decide⟩,⟨1749,by decide⟩] | 6 => ![⟨2807,by decide⟩,⟨2806,by decide⟩,⟨1429,by decide⟩] | _ => ![⟨2767,by decide⟩,⟨2808,by decide⟩,⟨2809,by decide⟩]

def ntree10RLRLRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRLRRRLL i else ntree10RLRLRRRLR (i - 8)

def ntree10RLRLRRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2355,by decide⟩,⟨2355,by decide⟩,⟨2810,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨2811,by decide⟩] | 2 => ![⟨2733,by decide⟩,⟨2409,by decide⟩,⟨2812,by decide⟩] | 3 => ![⟨2769,by decide⟩,⟨308,by decide⟩,⟨2813,by decide⟩] | 4 => ![⟨2355,by decide⟩,⟨2814,by decide⟩,⟨2814,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨2815,by decide⟩,⟨2815,by decide⟩] | 6 => ![⟨2585,by decide⟩,⟨2808,by decide⟩,⟨2808,by decide⟩] | _ => ![⟨2585,by decide⟩,⟨2816,by decide⟩,⟨2816,by decide⟩]

def ntree10RLRLRRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2426,by decide⟩,⟨2426,by decide⟩,⟨2810,by decide⟩] | 1 => ![⟨2428,by decide⟩,⟨2428,by decide⟩,⟨2811,by decide⟩] | 2 => ![⟨2817,by decide⟩,⟨2427,by decide⟩,⟨2812,by decide⟩] | 3 => ![⟨2818,by decide⟩,⟨2429,by decide⟩,⟨2813,by decide⟩] | 4 => ![⟨2725,by decide⟩,⟨2725,by decide⟩,⟨1711,by decide⟩] | 5 => ![⟨2819,by decide⟩,⟨2728,by decide⟩,⟨2820,by decide⟩] | 6 => ![⟨2821,by decide⟩,⟨2821,by decide⟩,⟨1988,by decide⟩] | _ => ![⟨2821,by decide⟩,⟨2822,by decide⟩,⟨2823,by decide⟩]

def ntree10RLRLRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRLRRRRL i else ntree10RLRLRRRRR (i - 8)

def ntree10RLRLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RLRLRRRL i else ntree10RLRLRRRR (i - 16)

def ntree10RLRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RLRLRRL i else ntree10RLRLRRR (i - 31)

def ntree10RLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10RLRLRL i else ntree10RLRLRR (i - 63)

def ntree10RLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 126 then ntree10RLRLL i else ntree10RLRLR (i - 126)

def ntree10RLRRLLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2824,by decide⟩,⟨2367,by decide⟩,⟨2825,by decide⟩] | 1 => ![⟨2824,by decide⟩,⟨2355,by decide⟩,⟨2824,by decide⟩] | 2 => ![⟨2355,by decide⟩,⟨2727,by decide⟩,⟨2727,by decide⟩] | 3 => ![⟨2826,by decide⟩,⟨1332,by decide⟩,⟨2820,by decide⟩] | 4 => ![⟨2689,by decide⟩,⟨1634,by decide⟩,⟨2693,by decide⟩] | 5 => ![⟨2729,by decide⟩,⟨2355,by decide⟩,⟨2784,by decide⟩] | _ => ![⟨2729,by decide⟩,⟨2355,by decide⟩,⟨2729,by decide⟩]

def ntree10RLRRLLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2827,by decide⟩,⟨595,by decide⟩,⟨2828,by decide⟩] | 1 => ![⟨2827,by decide⟩,⟨15,by decide⟩,⟨2827,by decide⟩] | 2 => ![⟨1988,by decide⟩,⟨2829,by decide⟩,⟨2829,by decide⟩] | 3 => ![⟨1988,by decide⟩,⟨2823,by decide⟩,⟨2823,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨2830,by decide⟩,⟨2830,by decide⟩] | 5 => ![⟨2831,by decide⟩,⟨2443,by decide⟩,⟨2825,by decide⟩] | 6 => ![⟨2824,by decide⟩,⟨2444,by decide⟩,⟨2824,by decide⟩] | _ => ![⟨2832,by decide⟩,⟨2446,by decide⟩,⟨2828,by decide⟩]

def ntree10RLRRLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RLRRLLLLL i else ntree10RLRRLLLLR (i - 7)

def ntree10RLRRLLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2827,by decide⟩,⟨2447,by decide⟩,⟨2827,by decide⟩] | 1 => ![⟨2355,by decide⟩,⟨2745,by decide⟩,⟨2833,by decide⟩] | 2 => ![⟨2725,by decide⟩,⟨2746,by decide⟩,⟨1815,by decide⟩] | 3 => ![⟨2392,by decide⟩,⟨2834,by decide⟩,⟨2745,by decide⟩] | 4 => ![⟨2724,by decide⟩,⟨2835,by decide⟩,⟨2409,by decide⟩] | 5 => ![⟨2821,by decide⟩,⟨2836,by decide⟩,⟨2018,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨2837,by decide⟩] | _ => ![⟨2355,by decide⟩,⟨2838,by decide⟩,⟨2838,by decide⟩]

def ntree10RLRRLLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1988,by decide⟩,⟨2030,by decide⟩,⟨2030,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨2839,by decide⟩,⟨2839,by decide⟩] | 2 => ![⟨2840,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩] | 3 => ![⟨2841,by decide⟩,⟨2454,by decide⟩,⟨2037,by decide⟩] | 4 => ![⟨2445,by decide⟩,⟨2445,by decide⟩,⟨2837,by decide⟩] | 5 => ![⟨2842,by decide⟩,⟨308,by decide⟩,⟨308,by decide⟩] | 6 => ![⟨2843,by decide⟩,⟨2455,by decide⟩,⟨1942,by decide⟩] | _ => ![⟨2355,by decide⟩,⟨2355,by decide⟩,⟨2778,by decide⟩]

def ntree10RLRRLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRRLLLRL i else ntree10RLRRLLLRR (i - 8)

def ntree10RLRRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RLRRLLLL i else ntree10RLRRLLLR (i - 15)

def ntree10RLRRLLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2781,by decide⟩,⟨2764,by decide⟩,⟨2833,by decide⟩] | 1 => ![⟨2045,by decide⟩,⟨2045,by decide⟩,⟨1988,by decide⟩] | 2 => ![⟨2715,by decide⟩,⟨2585,by decide⟩,⟨2715,by decide⟩] | 3 => ![⟨2689,by decide⟩,⟨308,by decide⟩,⟨2844,by decide⟩] | 4 => ![⟨2845,by decide⟩,⟨979,by decide⟩,⟨2846,by decide⟩] | 5 => ![⟨2847,by decide⟩,⟨2848,by decide⟩,⟨2848,by decide⟩] | 6 => ![⟨2849,by decide⟩,⟨2426,by decide⟩,⟨2824,by decide⟩] | _ => ![⟨2850,by decide⟩,⟨2459,by decide⟩,⟨2690,by decide⟩]

def ntree10RLRRLLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2851,by decide⟩,⟨1965,by decide⟩,⟨2844,by decide⟩] | 1 => ![⟨2852,by decide⟩,⟨2461,by decide⟩,⟨2846,by decide⟩] | 2 => ![⟨2853,by decide⟩,⟨2853,by decide⟩,⟨2853,by decide⟩] | 3 => ![⟨2854,by decide⟩,⟨2854,by decide⟩,⟨2853,by decide⟩] | 4 => ![⟨2855,by decide⟩,⟨2855,by decide⟩,⟨2856,by decide⟩] | 5 => ![⟨2857,by decide⟩,⟨2464,by decide⟩,⟨2729,by decide⟩] | 6 => ![⟨1845,by decide⟩,⟨2186,by decide⟩,⟨2731,by decide⟩] | _ => ![⟨2853,by decide⟩,⟨2858,by decide⟩,⟨2858,by decide⟩]

def ntree10RLRRLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRRLLRLL i else ntree10RLRRLLRLR (i - 8)

def ntree10RLRRLLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2855,by decide⟩,⟨2859,by decide⟩,⟨2860,by decide⟩] | 1 => ![⟨2861,by decide⟩,⟨2464,by decide⟩,⟨2733,by decide⟩] | 2 => ![⟨2862,by decide⟩,⟨2469,by decide⟩,⟨2736,by decide⟩] | 3 => ![⟨2853,by decide⟩,⟨2863,by decide⟩,⟨2863,by decide⟩] | 4 => ![⟨2856,by decide⟩,⟨2864,by decide⟩,⟨2864,by decide⟩] | 5 => ![⟨2865,by decide⟩,⟨2853,by decide⟩,⟨2865,by decide⟩] | 6 => ![⟨2866,by decide⟩,⟨2856,by decide⟩,⟨2866,by decide⟩] | _ => ![⟨2867,by decide⟩,⟨2868,by decide⟩,⟨2868,by decide⟩]

def ntree10RLRRLLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2867,by decide⟩,⟨2867,by decide⟩,⟨2867,by decide⟩] | 1 => ![⟨2869,by decide⟩,⟨2870,by decide⟩,⟨2870,by decide⟩] | 2 => ![⟨2869,by decide⟩,⟨2869,by decide⟩,⟨2869,by decide⟩] | 3 => ![⟨2871,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩] | 4 => ![⟨2076,by decide⟩,⟨15,by decide⟩,⟨1361,by decide⟩] | 5 => ![⟨2872,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩] | 6 => ![⟨2873,by decide⟩,⟨2365,by decide⟩,⟨2365,by decide⟩] | _ => ![⟨2080,by decide⟩,⟨1637,by decide⟩,⟨2757,by decide⟩]

def ntree10RLRRLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRRLLRRL i else ntree10RLRRLLRRR (i - 8)

def ntree10RLRRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RLRRLLRL i else ntree10RLRRLLRR (i - 16)

def ntree10RLRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RLRRLLL i else ntree10RLRRLLR (i - 31)

def ntree10RLRRLRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2856,by decide⟩,⟨2856,by decide⟩,⟨2856,by decide⟩] | 1 => ![⟨2874,by decide⟩,⟨2856,by decide⟩,⟨2874,by decide⟩] | 2 => ![⟨2355,by decide⟩,⟨2875,by decide⟩,⟨2875,by decide⟩] | 3 => ![⟨2876,by decide⟩,⟨2355,by decide⟩,⟨2733,by decide⟩] | 4 => ![⟨2877,by decide⟩,⟨13,by decide⟩,⟨2769,by decide⟩] | 5 => ![⟨2094,by decide⟩,⟨595,by decide⟩,⟨1340,by decide⟩] | _ => ![⟨418,by decide⟩,⟨13,by decide⟩,⟨2770,by decide⟩]

def ntree10RLRRLRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2078,by decide⟩,⟨596,by decide⟩,⟨2771,by decide⟩] | 1 => ![⟨2594,by decide⟩,⟨15,by decide⟩,⟨2594,by decide⟩] | 2 => ![⟨2878,by decide⟩,⟨2879,by decide⟩,⟨2879,by decide⟩] | 3 => ![⟨2878,by decide⟩,⟨2878,by decide⟩,⟨2878,by decide⟩] | 4 => ![⟨2880,by decide⟩,⟨2881,by decide⟩,⟨2881,by decide⟩] | 5 => ![⟨2880,by decide⟩,⟨2880,by decide⟩,⟨2880,by decide⟩] | 6 => ![⟨2853,by decide⟩,⟨2853,by decide⟩,⟨2882,by decide⟩] | _ => ![⟨2856,by decide⟩,⟨2856,by decide⟩,⟨2883,by decide⟩]

def ntree10RLRRLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RLRRLRLLL i else ntree10RLRRLRLLR (i - 7)

def ntree10RLRRLRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2884,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩] | 1 => ![⟨1236,by decide⟩,⟨2499,by decide⟩,⟨1711,by decide⟩] | 2 => ![⟨2885,by decide⟩,⟨15,by decide⟩,⟨1845,by decide⟩] | 3 => ![⟨2856,by decide⟩,⟨2886,by decide⟩,⟨2856,by decide⟩] | 4 => ![⟨2887,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩] | 5 => ![⟨2888,by decide⟩,⟨15,by decide⟩,⟨191,by decide⟩] | 6 => ![⟨2889,by decide⟩,⟨2365,by decide⟩,⟨2365,by decide⟩] | _ => ![⟨2890,by decide⟩,⟨1637,by decide⟩,⟨1860,by decide⟩]

def ntree10RLRRLRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2865,by decide⟩,⟨2853,by decide⟩,⟨2891,by decide⟩] | 1 => ![⟨2866,by decide⟩,⟨2856,by decide⟩,⟨2892,by decide⟩] | 2 => ![⟨2893,by decide⟩,⟨2355,by decide⟩,⟨2778,by decide⟩] | 3 => ![⟨2853,by decide⟩,⟨2894,by decide⟩,⟨2894,by decide⟩] | 4 => ![⟨2856,by decide⟩,⟨2895,by decide⟩,⟨2895,by decide⟩] | 5 => ![⟨2896,by decide⟩,⟨2355,by decide⟩,⟨2778,by decide⟩] | 6 => ![⟨2897,by decide⟩,⟨2365,by decide⟩,⟨2788,by decide⟩] | _ => ![⟨2853,by decide⟩,⟨2898,by decide⟩,⟨2898,by decide⟩]

def ntree10RLRRLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRRLRLRL i else ntree10RLRRLRLRR (i - 8)

def ntree10RLRRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RLRRLRLL i else ntree10RLRRLRLR (i - 15)

def ntree10RLRRLRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2874,by decide⟩,⟨2899,by decide⟩,⟨2900,by decide⟩] | 1 => ![⟨2867,by decide⟩,⟨2901,by decide⟩,⟨2901,by decide⟩] | 2 => ![⟨2869,by decide⟩,⟨2902,by decide⟩,⟨2902,by decide⟩] | 3 => ![⟨2903,by decide⟩,⟨2904,by decide⟩,⟨1711,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨1776,by decide⟩] | 5 => ![⟨2905,by decide⟩,⟨2906,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨2887,by decide⟩,⟨2355,by decide⟩,⟨2810,by decide⟩] | _ => ![⟨2907,by decide⟩,⟨692,by decide⟩,⟨2811,by decide⟩]

def ntree10RLRRLRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2908,by decide⟩,⟨1112,by decide⟩,⟨1924,by decide⟩] | 1 => ![⟨2888,by decide⟩,⟨308,by decide⟩,⟨340,by decide⟩] | 2 => ![⟨2909,by decide⟩,⟨1114,by decide⟩,⟨1942,by decide⟩] | 3 => ![⟨2733,by decide⟩,⟨2910,by decide⟩,⟨2911,by decide⟩] | 4 => ![⟨2594,by decide⟩,⟨2685,by decide⟩,⟨2678,by decide⟩] | 5 => ![⟨2878,by decide⟩,⟨2912,by decide⟩,⟨2912,by decide⟩] | 6 => ![⟨2880,by decide⟩,⟨2913,by decide⟩,⟨2913,by decide⟩] | _ => ![⟨2855,by decide⟩,⟨2855,by decide⟩,⟨2883,by decide⟩]

def ntree10RLRRLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRRLRRLL i else ntree10RLRRLRRLR (i - 8)

def ntree10RLRRLRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2914,by decide⟩,⟨2464,by decide⟩,⟨2824,by decide⟩] | 1 => ![⟨2915,by decide⟩,⟨13,by decide⟩,⟨2827,by decide⟩] | 2 => ![⟨2916,by decide⟩,⟨2863,by decide⟩,⟨2917,by decide⟩] | 3 => ![⟨2916,by decide⟩,⟨2853,by decide⟩,⟨2916,by decide⟩] | 4 => ![⟨2918,by decide⟩,⟨2864,by decide⟩,⟨2919,by decide⟩] | 5 => ![⟨2871,by decide⟩,⟨2541,by decide⟩,⟨2778,by decide⟩] | 6 => ![⟨2853,by decide⟩,⟨2920,by decide⟩,⟨2853,by decide⟩] | _ => ![⟨2854,by decide⟩,⟨2921,by decide⟩,⟨2894,by decide⟩]

def ntree10RLRRLRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2855,by decide⟩,⟨2922,by decide⟩,⟨2895,by decide⟩] | 1 => ![⟨2923,by decide⟩,⟨567,by decide⟩,⟨2837,by decide⟩] | 2 => ![⟨2924,by decide⟩,⟨2856,by decide⟩,⟨2925,by decide⟩] | 3 => ![⟨2926,by decide⟩,⟨1149,by decide⟩,⟨2690,by decide⟩] | 4 => ![⟨2691,by decide⟩,⟨555,by decide⟩,⟨2844,by decide⟩] | 5 => ![⟨2927,by decide⟩,⟨1151,by decide⟩,⟨2846,by decide⟩] | 6 => ![⟨2824,by decide⟩,⟨2355,by decide⟩,⟨2928,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨2929,by decide⟩]

def ntree10RLRRLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRRLRRRL i else ntree10RLRRLRRRR (i - 8)

def ntree10RLRRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RLRRLRRL i else ntree10RLRRLRRR (i - 16)

def ntree10RLRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RLRRLRL i else ntree10RLRRLRR (i - 31)

def ntree10RLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10RLRRLL i else ntree10RLRRLR (i - 63)

def ntree10RLRRRLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3,by decide⟩,⟨2930,by decide⟩,⟨2931,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨1616,by decide⟩,⟨2932,by decide⟩] | 2 => ![⟨7,by decide⟩,⟨1618,by decide⟩,⟨2933,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨1622,by decide⟩,⟨2934,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨2935,by decide⟩,⟨2936,by decide⟩] | 5 => ![⟨3,by decide⟩,⟨3,by decide⟩,⟨2931,by decide⟩] | _ => ![⟨14,by decide⟩,⟨1628,by decide⟩,⟨2936,by decide⟩]

def ntree10RLRRRLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨9,by decide⟩,⟨9,by decide⟩,⟨2937,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨2938,by decide⟩,⟨2939,by decide⟩] | 2 => ![⟨16,by decide⟩,⟨1631,by decide⟩,⟨2940,by decide⟩] | 3 => ![⟨18,by decide⟩,⟨1634,by decide⟩,⟨2941,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨2939,by decide⟩] | 5 => ![⟨1635,by decide⟩,⟨1635,by decide⟩,⟨2942,by decide⟩] | 6 => ![⟨1637,by decide⟩,⟨1637,by decide⟩,⟨2943,by decide⟩] | _ => ![⟨1637,by decide⟩,⟨1637,by decide⟩,⟨2943,by decide⟩]

def ntree10RLRRRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RLRRRLLLL i else ntree10RLRRRLLLR (i - 7)

def ntree10RLRRRLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2944,by decide⟩,⟨1637,by decide⟩,⟨2944,by decide⟩] | 1 => ![⟨2944,by decide⟩,⟨1642,by decide⟩,⟨2945,by decide⟩] | 2 => ![⟨9,by decide⟩,⟨9,by decide⟩,⟨2946,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨2938,by decide⟩,⟨2947,by decide⟩] | 4 => ![⟨8,by decide⟩,⟨1644,by decide⟩,⟨2948,by decide⟩] | 5 => ![⟨14,by decide⟩,⟨1646,by decide⟩,⟨2949,by decide⟩] | 6 => ![⟨14,by decide⟩,⟨2938,by decide⟩,⟨14,by decide⟩] | _ => ![⟨1637,by decide⟩,⟨1637,by decide⟩,⟨2950,by decide⟩]

def ntree10RLRRRLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1637,by decide⟩,⟨2951,by decide⟩,⟨2950,by decide⟩] | 1 => ![⟨2952,by decide⟩,⟨1637,by decide⟩,⟨2952,by decide⟩] | 2 => ![⟨2952,by decide⟩,⟨1650,by decide⟩,⟨2953,by decide⟩] | 3 => ![⟨2952,by decide⟩,⟨2951,by decide⟩,⟨2952,by decide⟩] | 4 => ![⟨1637,by decide⟩,⟨2951,by decide⟩,⟨1637,by decide⟩] | 5 => ![⟨2954,by decide⟩,⟨1651,by decide⟩,⟨2954,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨2955,by decide⟩,⟨0,by decide⟩] | _ => ![⟨2956,by decide⟩,⟨2955,by decide⟩,⟨2929,by decide⟩]

def ntree10RLRRRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRRRLLRL i else ntree10RLRRRLLRR (i - 8)

def ntree10RLRRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RLRRRLLL i else ntree10RLRRRLLR (i - 15)

def ntree10RLRRRLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2957,by decide⟩,⟨2958,by decide⟩,⟨2931,by decide⟩] | 1 => ![⟨3,by decide⟩,⟨1655,by decide⟩,⟨2959,by decide⟩] | 2 => ![⟨9,by decide⟩,⟨2960,by decide⟩,⟨1656,by decide⟩] | 3 => ![⟨2961,by decide⟩,⟨2962,by decide⟩,⟨2937,by decide⟩] | 4 => ![⟨2963,by decide⟩,⟨2964,by decide⟩,⟨2965,by decide⟩] | 5 => ![⟨3,by decide⟩,⟨2966,by decide⟩,⟨3,by decide⟩] | 6 => ![⟨2967,by decide⟩,⟨2966,by decide⟩,⟨2931,by decide⟩] | _ => ![⟨15,by decide⟩,⟨2968,by decide⟩,⟨1661,by decide⟩]

def ntree10RLRRRLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2969,by decide⟩,⟨2970,by decide⟩,⟨2939,by decide⟩] | 1 => ![⟨9,by decide⟩,⟨2962,by decide⟩,⟨9,by decide⟩] | 2 => ![⟨2963,by decide⟩,⟨2971,by decide⟩,⟨2939,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨1663,by decide⟩,⟨2965,by decide⟩] | 4 => ![⟨3,by decide⟩,⟨2958,by decide⟩,⟨3,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨2964,by decide⟩,⟨1663,by decide⟩] | 6 => ![⟨1637,by decide⟩,⟨2972,by decide⟩,⟨1637,by decide⟩] | _ => ![⟨2973,by decide⟩,⟨2972,by decide⟩,⟨2943,by decide⟩]

def ntree10RLRRRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRRRLRLL i else ntree10RLRRRLRLR (i - 8)

def ntree10RLRRRLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1637,by decide⟩,⟨1666,by decide⟩,⟨2974,by decide⟩] | 1 => ![⟨1637,by decide⟩,⟨2975,by decide⟩,⟨1666,by decide⟩] | 2 => ![⟨2973,by decide⟩,⟨2975,by decide⟩,⟨2974,by decide⟩] | 3 => ![⟨2976,by decide⟩,⟨2962,by decide⟩,⟨2946,by decide⟩] | 4 => ![⟨2977,by decide⟩,⟨2971,by decide⟩,⟨2947,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨1671,by decide⟩,⟨2978,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨2971,by decide⟩,⟨15,by decide⟩] | _ => ![⟨1637,by decide⟩,⟨2979,by decide⟩,⟨1637,by decide⟩]

def ntree10RLRRRLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2980,by decide⟩,⟨2979,by decide⟩,⟨2950,by decide⟩] | 1 => ![⟨1651,by decide⟩,⟨2981,by decide⟩,⟨1651,by decide⟩] | 2 => ![⟨1637,by decide⟩,⟨2972,by decide⟩,⟨1637,by decide⟩] | 3 => ![⟨3,by decide⟩,⟨2958,by decide⟩,⟨2982,by decide⟩] | 4 => ![⟨2957,by decide⟩,⟨2983,by decide⟩,⟨2984,by decide⟩] | 5 => ![⟨7,by decide⟩,⟨1655,by decide⟩,⟨2985,by decide⟩] | 6 => ![⟨7,by decide⟩,⟨1680,by decide⟩,⟨2986,by decide⟩] | _ => ![⟨14,by decide⟩,⟨2964,by decide⟩,⟨2987,by decide⟩]

def ntree10RLRRRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRRRLRRL i else ntree10RLRRRLRRR (i - 8)

def ntree10RLRRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RLRRRLRL i else ntree10RLRRRLRR (i - 16)

def ntree10RLRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RLRRRLL i else ntree10RLRRRLR (i - 31)

def ntree10RLRRRRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2988,by decide⟩,⟨2989,by decide⟩,⟨2936,by decide⟩] | 1 => ![⟨2988,by decide⟩,⟨2990,by decide⟩,⟨2991,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨2971,by decide⟩,⟨2992,by decide⟩] | 3 => ![⟨2963,by decide⟩,⟨2993,by decide⟩,⟨2994,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨1663,by decide⟩,⟨2987,by decide⟩] | 5 => ![⟨14,by decide⟩,⟨1685,by decide⟩,⟨2991,by decide⟩] | _ => ![⟨2995,by decide⟩,⟨2996,by decide⟩,⟨2939,by decide⟩]

def ntree10RLRRRRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨2971,by decide⟩,⟨81,by decide⟩] | 1 => ![⟨2997,by decide⟩,⟨1663,by decide⟩,⟨2998,by decide⟩] | 2 => ![⟨2997,by decide⟩,⟨84,by decide⟩,⟨2999,by decide⟩] | 3 => ![⟨2997,by decide⟩,⟨2964,by decide⟩,⟨2998,by decide⟩] | 4 => ![⟨3000,by decide⟩,⟨3001,by decide⟩,⟨2999,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨2971,by decide⟩,⟨3002,by decide⟩] | 6 => ![⟨2977,by decide⟩,⟨2993,by decide⟩,⟨3003,by decide⟩] | _ => ![⟨14,by decide⟩,⟨1671,by decide⟩,⟨3004,by decide⟩]

def ntree10RLRRRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RLRRRRLLL i else ntree10RLRRRRLLR (i - 7)

def ntree10RLRRRRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨14,by decide⟩,⟨1689,by decide⟩,⟨3005,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨2971,by decide⟩,⟨14,by decide⟩] | 2 => ![⟨14,by decide⟩,⟨2993,by decide⟩,⟨14,by decide⟩] | 3 => ![⟨3006,by decide⟩,⟨68,by decide⟩,⟨2947,by decide⟩] | 4 => ![⟨1695,by decide⟩,⟨3007,by decide⟩,⟨1695,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨2993,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨3008,by decide⟩,⟨1695,by decide⟩,⟨3008,by decide⟩] | _ => ![⟨3008,by decide⟩,⟨3007,by decide⟩,⟨3008,by decide⟩]

def ntree10RLRRRRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨91,by decide⟩,⟨3009,by decide⟩,⟨1699,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨1707,by decide⟩,⟨3010,by decide⟩] | 2 => ![⟨96,by decide⟩,⟨3011,by decide⟩,⟨3012,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨1712,by decide⟩,⟨3012,by decide⟩] | 4 => ![⟨99,by decide⟩,⟨3013,by decide⟩,⟨1715,by decide⟩] | 5 => ![⟨18,by decide⟩,⟨1724,by decide⟩,⟨3014,by decide⟩] | 6 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨3015,by decide⟩] | _ => ![⟨3016,by decide⟩,⟨3016,by decide⟩,⟨1635,by decide⟩]

def ntree10RLRRRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRRRRLRL i else ntree10RLRRRRLRR (i - 8)

def ntree10RLRRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RLRRRRLL i else ntree10RLRRRRLR (i - 15)

def ntree10RLRRRRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3017,by decide⟩,⟨3017,by decide⟩,⟨1637,by decide⟩] | 1 => ![⟨1637,by decide⟩,⟨1637,by decide⟩,⟨3018,by decide⟩] | 2 => ![⟨3017,by decide⟩,⟨3017,by decide⟩,⟨3018,by decide⟩] | 3 => ![⟨3019,by decide⟩,⟨3019,by decide⟩,⟨1637,by decide⟩] | 4 => ![⟨3020,by decide⟩,⟨3019,by decide⟩,⟨2944,by decide⟩] | 5 => ![⟨97,by decide⟩,⟨3011,by decide⟩,⟨1712,by decide⟩] | 6 => ![⟨3017,by decide⟩,⟨3021,by decide⟩,⟨1730,by decide⟩] | _ => ![⟨3022,by decide⟩,⟨3017,by decide⟩,⟨2952,by decide⟩]

def ntree10RLRRRRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2952,by decide⟩,⟨1730,by decide⟩,⟨3023,by decide⟩] | 1 => ![⟨3022,by decide⟩,⟨3021,by decide⟩,⟨3023,by decide⟩] | 2 => ![⟨90,by decide⟩,⟨3024,by decide⟩,⟨1734,by decide⟩] | 3 => ![⟨91,by decide⟩,⟨3025,by decide⟩,⟨1736,by decide⟩] | 4 => ![⟨95,by decide⟩,⟨3026,by decide⟩,⟨1739,by decide⟩] | 5 => ![⟨9,by decide⟩,⟨2962,by decide⟩,⟨3027,by decide⟩] | 6 => ![⟨97,by decide⟩,⟨3028,by decide⟩,⟨3029,by decide⟩] | _ => ![⟨91,by decide⟩,⟨3030,by decide⟩,⟨1743,by decide⟩]

def ntree10RLRRRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRRRRRLL i else ntree10RLRRRRRLR (i - 8)

def ntree10RLRRRRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨97,by decide⟩,⟨3031,by decide⟩,⟨1745,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨2970,by decide⟩,⟨3015,by decide⟩] | 2 => ![⟨98,by decide⟩,⟨3032,by decide⟩,⟨1747,by decide⟩] | 3 => ![⟨99,by decide⟩,⟨3033,by decide⟩,⟨1749,by decide⟩] | 4 => ![⟨97,by decide⟩,⟨3028,by decide⟩,⟨1751,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨2971,by decide⟩,⟨3015,by decide⟩] | 6 => ![⟨3019,by decide⟩,⟨3034,by decide⟩,⟨1752,by decide⟩] | _ => ![⟨3017,by decide⟩,⟨3035,by decide⟩,⟨1754,by decide⟩]

def ntree10RLRRRRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1637,by decide⟩,⟨2979,by decide⟩,⟨3018,by decide⟩] | 1 => ![⟨3,by decide⟩,⟨3036,by decide⟩,⟨1699,by decide⟩] | 2 => ![⟨91,by decide⟩,⟨3037,by decide⟩,⟨1757,by decide⟩] | 3 => ![⟨96,by decide⟩,⟨3028,by decide⟩,⟨3038,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨3039,by decide⟩,⟨3012,by decide⟩] | 5 => ![⟨96,by decide⟩,⟨3040,by decide⟩,⟨3041,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨3042,by decide⟩,⟨1715,by decide⟩] | _ => ![⟨99,by decide⟩,⟨3043,by decide⟩,⟨1768,by decide⟩]

def ntree10RLRRRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RLRRRRRRL i else ntree10RLRRRRRRR (i - 8)

def ntree10RLRRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RLRRRRRL i else ntree10RLRRRRRR (i - 16)

def ntree10RLRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RLRRRRL i else ntree10RLRRRRR (i - 31)

def ntree10RLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10RLRRRL i else ntree10RLRRRR (i - 63)

def ntree10RLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 126 then ntree10RLRRL i else ntree10RLRRR (i - 126)

def ntree10RLR (i : Nat) : Fin 3 → Fin 3959 := if i < 252 then ntree10RLRL i else ntree10RLRR (i - 252)

def ntree10RL (i : Nat) : Fin 3 → Fin 3959 := if i < 504 then ntree10RLL i else ntree10RLR (i - 504)

def ntree10RRLLLLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨3015,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨3044,by decide⟩,⟨109,by decide⟩] | 2 => ![⟨3045,by decide⟩,⟨99,by decide⟩,⟨2997,by decide⟩] | 3 => ![⟨2997,by decide⟩,⟨15,by decide⟩,⟨2997,by decide⟩] | 4 => ![⟨2997,by decide⟩,⟨2971,by decide⟩,⟨2997,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨3039,by decide⟩,⟨1712,by decide⟩] | _ => ![⟨97,by decide⟩,⟨3040,by decide⟩,⟨1775,by decide⟩]

def ntree10RRLLLLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨3046,by decide⟩,⟨1712,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨3046,by decide⟩,⟨3012,by decide⟩] | 2 => ![⟨9,by decide⟩,⟨1707,by decide⟩,⟨3047,by decide⟩] | 3 => ![⟨97,by decide⟩,⟨3011,by decide⟩,⟨3048,by decide⟩] | 4 => ![⟨96,by decide⟩,⟨3049,by decide⟩,⟨2936,by decide⟩] | 5 => ![⟨8,by decide⟩,⟨1790,by decide⟩,⟨3050,by decide⟩] | 6 => ![⟨96,by decide⟩,⟨3051,by decide⟩,⟨3052,by decide⟩] | _ => ![⟨15,by decide⟩,⟨1712,by decide⟩,⟨3048,by decide⟩]

def ntree10RRLLLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RRLLLLLLL i else ntree10RRLLLLLLR (i - 7)

def ntree10RRLLLLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨14,by decide⟩,⟨1796,by decide⟩,⟨3052,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨1724,by decide⟩,⟨3053,by decide⟩] | 2 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨2939,by decide⟩] | 3 => ![⟨18,by decide⟩,⟨1801,by decide⟩,⟨3054,by decide⟩] | 4 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨3055,by decide⟩] | 5 => ![⟨3056,by decide⟩,⟨3056,by decide⟩,⟨1802,by decide⟩] | 6 => ![⟨1802,by decide⟩,⟨1802,by decide⟩,⟨3057,by decide⟩] | _ => ![⟨3056,by decide⟩,⟨3056,by decide⟩,⟨3057,by decide⟩]

def ntree10RRLLLLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨3055,by decide⟩] | 1 => ![⟨3058,by decide⟩,⟨3058,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨109,by decide⟩,⟨3059,by decide⟩] | 3 => ![⟨3058,by decide⟩,⟨3058,by decide⟩,⟨2939,by decide⟩] | 4 => ![⟨3060,by decide⟩,⟨3058,by decide⟩,⟨18,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨1712,by decide⟩,⟨3061,by decide⟩] | 6 => ![⟨97,by decide⟩,⟨3011,by decide⟩,⟨3061,by decide⟩] | _ => ![⟨15,by decide⟩,⟨2938,by decide⟩,⟨15,by decide⟩]

def ntree10RRLLLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLLLLLRL i else ntree10RRLLLLLRR (i - 8)

def ntree10RRLLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RRLLLLLL i else ntree10RRLLLLLR (i - 15)

def ntree10RRLLLLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3062,by decide⟩,⟨3028,by decide⟩,⟨3063,by decide⟩] | 1 => ![⟨95,by decide⟩,⟨3064,by decide⟩,⟨1656,by decide⟩] | 2 => ![⟨9,by decide⟩,⟨3065,by decide⟩,⟨2937,by decide⟩] | 3 => ![⟨97,by decide⟩,⟨3066,by decide⟩,⟨2965,by decide⟩] | 4 => ![⟨95,by decide⟩,⟨3067,by decide⟩,⟨1816,by decide⟩] | 5 => ![⟨2961,by decide⟩,⟨3068,by decide⟩,⟨3069,by decide⟩] | 6 => ![⟨3062,by decide⟩,⟨3070,by decide⟩,⟨3071,by decide⟩] | _ => ![⟨97,by decide⟩,⟨3072,by decide⟩,⟨1661,by decide⟩]

def ntree10RRLLLLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨3073,by decide⟩,⟨2939,by decide⟩] | 1 => ![⟨97,by decide⟩,⟨3074,by decide⟩,⟨1821,by decide⟩] | 2 => ![⟨2969,by decide⟩,⟨3075,by decide⟩,⟨3055,by decide⟩] | 3 => ![⟨97,by decide⟩,⟨3066,by decide⟩,⟨1663,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨3076,by decide⟩,⟨2939,by decide⟩] | 5 => ![⟨97,by decide⟩,⟨3070,by decide⟩,⟨1823,by decide⟩] | 6 => ![⟨2963,by decide⟩,⟨3077,by decide⟩,⟨3055,by decide⟩] | _ => ![⟨3058,by decide⟩,⟨3078,by decide⟩,⟨166,by decide⟩]

def ntree10RRLLLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLLLLRLL i else ntree10RRLLLLRLR (i - 8)

def ntree10RRLLLLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3079,by decide⟩,⟨3078,by decide⟩,⟨3080,by decide⟩] | 1 => ![⟨3058,by decide⟩,⟨3081,by decide⟩,⟨1663,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨168,by decide⟩,⟨2939,by decide⟩] | 3 => ![⟨3058,by decide⟩,⟨3081,by decide⟩,⟨2965,by decide⟩] | 4 => ![⟨3082,by decide⟩,⟨2970,by decide⟩,⟨35,by decide⟩] | 5 => ![⟨3083,by decide⟩,⟨2971,by decide⟩,⟨3084,by decide⟩] | 6 => ![⟨97,by decide⟩,⟨3028,by decide⟩,⟨3085,by decide⟩] | _ => ![⟨2963,by decide⟩,⟨3039,by decide⟩,⟨3048,by decide⟩]

def ntree10RRLLLLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3062,by decide⟩,⟨3040,by decide⟩,⟨3086,by decide⟩] | 1 => ![⟨96,by decide⟩,⟨3066,by decide⟩,⟨2987,by decide⟩] | 2 => ![⟨14,by decide⟩,⟨3087,by decide⟩,⟨2936,by decide⟩] | 3 => ![⟨96,by decide⟩,⟨3088,by decide⟩,⟨2991,by decide⟩] | 4 => ![⟨96,by decide⟩,⟨3070,by decide⟩,⟨3089,by decide⟩] | 5 => ![⟨2988,by decide⟩,⟨3090,by decide⟩,⟨3052,by decide⟩] | 6 => ![⟨3091,by decide⟩,⟨3092,by decide⟩,⟨3093,by decide⟩] | _ => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨2939,by decide⟩]

def ntree10RRLLLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLLLLRRL i else ntree10RRLLLLRRR (i - 8)

def ntree10RRLLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RRLLLLRL i else ntree10RRLLLLRR (i - 16)

def ntree10RRLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RRLLLLL i else ntree10RRLLLLR (i - 31)

def ntree10RRLLLRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨2971,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨2963,by decide⟩,⟨3044,by decide⟩,⟨3059,by decide⟩] | 2 => ![⟨3094,by decide⟩,⟨1663,by decide⟩,⟨1663,by decide⟩] | 3 => ![⟨3095,by decide⟩,⟨1712,by decide⟩,⟨1712,by decide⟩] | 4 => ![⟨3,by decide⟩,⟨3,by decide⟩,⟨3096,by decide⟩] | 5 => ![⟨7,by decide⟩,⟨1631,by decide⟩,⟨3097,by decide⟩] | _ => ![⟨14,by decide⟩,⟨1634,by decide⟩,⟨3098,by decide⟩]

def ntree10RRLLLRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨14,by decide⟩,⟨2003,by decide⟩,⟨3099,by decide⟩] | 1 => ![⟨3100,by decide⟩,⟨3100,by decide⟩,⟨3101,by decide⟩] | 2 => ![⟨3102,by decide⟩,⟨3100,by decide⟩,⟨3103,by decide⟩] | 3 => ![⟨3104,by decide⟩,⟨3105,by decide⟩,⟨3098,by decide⟩] | 4 => ![⟨3104,by decide⟩,⟨3100,by decide⟩,⟨14,by decide⟩] | 5 => ![⟨187,by decide⟩,⟨3106,by decide⟩,⟨1631,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨1854,by decide⟩,⟨1854,by decide⟩] | _ => ![⟨193,by decide⟩,⟨3107,by decide⟩,⟨1634,by decide⟩]

def ntree10RRLLLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RRLLLRLLL i else ntree10RRLLLRLLR (i - 7)

def ntree10RRLLLRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1637,by decide⟩,⟨1861,by decide⟩,⟨1861,by decide⟩] | 1 => ![⟨3108,by decide⟩,⟨3108,by decide⟩,⟨1637,by decide⟩] | 2 => ![⟨3108,by decide⟩,⟨3109,by decide⟩,⟨1642,by decide⟩] | 3 => ![⟨201,by decide⟩,⟨201,by decide⟩,⟨3110,by decide⟩] | 4 => ![⟨214,by decide⟩,⟨3111,by decide⟩,⟨3112,by decide⟩] | 5 => ![⟨3113,by decide⟩,⟨3108,by decide⟩,⟨2952,by decide⟩] | 6 => ![⟨3114,by decide⟩,⟨2958,by decide⟩,⟨3096,by decide⟩] | _ => ![⟨3115,by decide⟩,⟨2971,by decide⟩,⟨3101,by decide⟩]

def ntree10RRLLLRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3116,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨3117,by decide⟩] | 2 => ![⟨3118,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨3119,by decide⟩,⟨2971,by decide⟩,⟨3119,by decide⟩] | 4 => ![⟨3120,by decide⟩,⟨3121,by decide⟩,⟨3122,by decide⟩] | 5 => ![⟨3100,by decide⟩,⟨3121,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨3100,by decide⟩,⟨3123,by decide⟩,⟨1663,by decide⟩] | _ => ![⟨187,by decide⟩,⟨3124,by decide⟩,⟨3,by decide⟩]

def ntree10RRLLLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLLLRLRL i else ntree10RRLLLRLRR (i - 8)

def ntree10RRLLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RRLLLRLL i else ntree10RRLLLRLR (i - 15)

def ntree10RRLLLRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨187,by decide⟩,⟨3125,by decide⟩,⟨1655,by decide⟩] | 1 => ![⟨193,by decide⟩,⟨3126,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨194,by decide⟩,⟨3127,by decide⟩,⟨1883,by decide⟩] | 3 => ![⟨1635,by decide⟩,⟨3128,by decide⟩,⟨1635,by decide⟩] | 4 => ![⟨1637,by decide⟩,⟨3129,by decide⟩,⟨1637,by decide⟩] | 5 => ![⟨3108,by decide⟩,⟨3130,by decide⟩,⟨1637,by decide⟩] | 6 => ![⟨3108,by decide⟩,⟨3131,by decide⟩,⟨1666,by decide⟩] | _ => ![⟨3132,by decide⟩,⟨2971,by decide⟩,⟨3132,by decide⟩]

def ntree10RRLLLRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3133,by decide⟩,⟨3134,by decide⟩,⟨3135,by decide⟩] | 1 => ![⟨201,by decide⟩,⟨3134,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨201,by decide⟩,⟨3136,by decide⟩,⟨1671,by decide⟩] | 3 => ![⟨195,by decide⟩,⟨3137,by decide⟩,⟨195,by decide⟩] | 4 => ![⟨3138,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 5 => ![⟨3102,by decide⟩,⟨3121,by decide⟩,⟨3139,by decide⟩] | 6 => ![⟨3104,by decide⟩,⟨3123,by decide⟩,⟨2987,by decide⟩] | _ => ![⟨257,by decide⟩,⟨3140,by decide⟩,⟨1852,by decide⟩]

def ntree10RRLLLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLLLRRLL i else ntree10RRLLLRRLR (i - 8)

def ntree10RRLLLRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨257,by decide⟩,⟨3141,by decide⟩,⟨1655,by decide⟩] | 1 => ![⟨260,by decide⟩,⟨3142,by decide⟩,⟨1900,by decide⟩] | 2 => ![⟨262,by decide⟩,⟨3143,by decide⟩,⟨262,by decide⟩] | 3 => ![⟨3144,by decide⟩,⟨3145,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨265,by decide⟩,⟨3146,by decide⟩,⟨1866,by decide⟩] | 5 => ![⟨265,by decide⟩,⟨3147,by decide⟩,⟨1663,by decide⟩] | 6 => ![⟨3100,by decide⟩,⟨3148,by decide⟩,⟨84,by decide⟩] | _ => ![⟨3149,by decide⟩,⟨3001,by decide⟩,⟨84,by decide⟩]

def ntree10RRLLLRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3150,by decide⟩,⟨3146,by decide⟩,⟨3151,by decide⟩] | 1 => ![⟨272,by decide⟩,⟨3152,by decide⟩,⟨3004,by decide⟩] | 2 => ![⟨3153,by decide⟩,⟨3143,by decide⟩,⟨3153,by decide⟩] | 3 => ![⟨3154,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨1724,by decide⟩,⟨3155,by decide⟩] | 5 => ![⟨3156,by decide⟩,⟨99,by decide⟩,⟨3103,by decide⟩] | 6 => ![⟨3157,by decide⟩,⟨3158,by decide⟩,⟨14,by decide⟩] | _ => ![⟨281,by decide⟩,⟨3159,by decide⟩,⟨1724,by decide⟩]

def ntree10RRLLLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLLLRRRL i else ntree10RRLLLRRRR (i - 8)

def ntree10RRLLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RRLLLRRL i else ntree10RRLLLRRR (i - 16)

def ntree10RRLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RRLLLRL i else ntree10RRLLLRR (i - 31)

def ntree10RRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10RRLLLL i else ntree10RRLLLR (i - 63)

def ntree10RRLLRLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3160,by decide⟩,⟨3160,by decide⟩,⟨1637,by decide⟩] | 1 => ![⟨304,by decide⟩,⟨3159,by decide⟩,⟨3155,by decide⟩] | 2 => ![⟨3161,by decide⟩,⟨3160,by decide⟩,⟨2952,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨2971,by decide⟩,⟨3162,by decide⟩] | 4 => ![⟨3163,by decide⟩,⟨3033,by decide⟩,⟨3164,by decide⟩] | 5 => ![⟨3165,by decide⟩,⟨2971,by decide⟩,⟨15,by decide⟩] | _ => ![⟨3158,by decide⟩,⟨3166,by decide⟩,⟨308,by decide⟩]

def ntree10RRLLRLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨91,by decide⟩,⟨3167,by decide⟩,⟨1946,by decide⟩] | 1 => ![⟨281,by decide⟩,⟨3168,by decide⟩,⟨1948,by decide⟩] | 2 => ![⟨282,by decide⟩,⟨3169,by decide⟩,⟨1950,by decide⟩] | 3 => ![⟨3016,by decide⟩,⟨3170,by decide⟩,⟨1952,by decide⟩] | 4 => ![⟨3017,by decide⟩,⟨3171,by decide⟩,⟨1954,by decide⟩] | 5 => ![⟨3019,by decide⟩,⟨3172,by decide⟩,⟨1954,by decide⟩] | 6 => ![⟨3160,by decide⟩,⟨3173,by decide⟩,⟨1954,by decide⟩] | _ => ![⟨3174,by decide⟩,⟨3028,by decide⟩,⟨3175,by decide⟩]

def ntree10RRLLRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RRLLRLLLL i else ntree10RRLLRLLLR (i - 7)

def ntree10RRLLRLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨97,by decide⟩,⟨3176,by decide⟩,⟨1948,by decide⟩] | 1 => ![⟨3177,by decide⟩,⟨3168,by decide⟩,⟨3178,by decide⟩] | 2 => ![⟨3179,by decide⟩,⟨2972,by decide⟩,⟨1637,by decide⟩] | 3 => ![⟨1918,by decide⟩,⟨2971,by decide⟩,⟨347,by decide⟩] | 4 => ![⟨3156,by decide⟩,⟨3033,by decide⟩,⟨3180,by decide⟩] | 5 => ![⟨3157,by decide⟩,⟨3166,by decide⟩,⟨331,by decide⟩] | 6 => ![⟨338,by decide⟩,⟨3181,by decide⟩,⟨1970,by decide⟩] | _ => ![⟨343,by decide⟩,⟨3182,by decide⟩,⟨15,by decide⟩]

def ntree10RRLLRLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3183,by decide⟩,⟨3181,by decide⟩,⟨3184,by decide⟩] | 1 => ![⟨3185,by decide⟩,⟨2971,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨3186,by decide⟩,⟨3182,by decide⟩,⟨14,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨1724,by decide⟩,⟨3187,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨1801,by decide⟩,⟨3188,by decide⟩] | 5 => ![⟨97,by decide⟩,⟨3189,by decide⟩,⟨2003,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨3190,by decide⟩,⟨15,by decide⟩] | _ => ![⟨96,by decide⟩,⟨3189,by decide⟩,⟨3099,by decide⟩]

def ntree10RRLLRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLLRLLRL i else ntree10RRLLRLLRR (i - 8)

def ntree10RRLLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RRLLRLLL i else ntree10RRLLRLLR (i - 15)

def ntree10RRLLRLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨14,by decide⟩,⟨3190,by decide⟩,⟨14,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨3191,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨1918,by decide⟩,⟨3192,by decide⟩,⟨3101,by decide⟩] | 3 => ![⟨3193,by decide⟩,⟨1988,by decide⟩,⟨3193,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨3191,by decide⟩,⟨14,by decide⟩] | 5 => ![⟨3157,by decide⟩,⟨3194,by decide⟩,⟨3098,by decide⟩] | 6 => ![⟨3195,by decide⟩,⟨3196,by decide⟩,⟨3193,by decide⟩] | _ => ![⟨97,by decide⟩,⟨3197,by decide⟩,⟨1866,by decide⟩]

def ntree10RRLLRLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨201,by decide⟩,⟨3198,by decide⟩,⟨1724,by decide⟩] | 1 => ![⟨201,by decide⟩,⟨3199,by decide⟩,⟨1634,by decide⟩] | 2 => ![⟨3056,by decide⟩,⟨3200,by decide⟩,⟨1999,by decide⟩] | 3 => ![⟨1802,by decide⟩,⟨3201,by decide⟩,⟨1802,by decide⟩] | 4 => ![⟨3058,by decide⟩,⟨3202,by decide⟩,⟨1866,by decide⟩] | 5 => ![⟨201,by decide⟩,⟨3203,by decide⟩,⟨109,by decide⟩] | 6 => ![⟨3204,by decide⟩,⟨3204,by decide⟩,⟨1988,by decide⟩] | _ => ![⟨3158,by decide⟩,⟨3194,by decide⟩,⟨1634,by decide⟩]

def ntree10RRLLRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLLRLRLL i else ntree10RRLLRLRLR (i - 8)

def ntree10RRLLRLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3196,by decide⟩,⟨3196,by decide⟩,⟨1988,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨3205,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨3206,by decide⟩,⟨201,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨3076,by decide⟩,⟨3101,by decide⟩] | 4 => ![⟨3115,by decide⟩,⟨3077,by decide⟩,⟨3207,by decide⟩] | 5 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨3117,by decide⟩] | 6 => ![⟨3208,by decide⟩,⟨308,by decide⟩,⟨308,by decide⟩] | _ => ![⟨1988,by decide⟩,⟨3209,by decide⟩,⟨1988,by decide⟩]

def ntree10RRLLRLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3210,by decide⟩,⟨1663,by decide⟩,⟨3211,by decide⟩] | 1 => ![⟨3210,by decide⟩,⟨308,by decide⟩,⟨3212,by decide⟩] | 2 => ![⟨3213,by decide⟩,⟨2964,by decide⟩,⟨3211,by decide⟩] | 3 => ![⟨3214,by decide⟩,⟨3166,by decide⟩,⟨3212,by decide⟩] | 4 => ![⟨3196,by decide⟩,⟨3215,by decide⟩,⟨2018,by decide⟩] | 5 => ![⟨362,by decide⟩,⟨3216,by decide⟩,⟨2020,by decide⟩] | 6 => ![⟨201,by decide⟩,⟨3217,by decide⟩,⟨2022,by decide⟩] | _ => ![⟨362,by decide⟩,⟨3218,by decide⟩,⟨2023,by decide⟩]

def ntree10RRLLRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLLRLRRL i else ntree10RRLLRLRRR (i - 8)

def ntree10RRLLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RRLLRLRL i else ntree10RRLLRLRR (i - 16)

def ntree10RRLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RRLLRLL i else ntree10RRLLRLR (i - 31)

def ntree10RRLLRRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨3077,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨3056,by decide⟩,⟨3219,by decide⟩,⟨2027,by decide⟩] | 2 => ![⟨3204,by decide⟩,⟨3220,by decide⟩,⟨2030,by decide⟩] | 3 => ![⟨3204,by decide⟩,⟨3221,by decide⟩,⟨2018,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨2971,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨14,by decide⟩,⟨3076,by decide⟩,⟨14,by decide⟩] | _ => ![⟨14,by decide⟩,⟨3077,by decide⟩,⟨14,by decide⟩]

def ntree10RRLLRRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1987,by decide⟩,⟨3209,by decide⟩,⟨3222,by decide⟩] | 1 => ![⟨3193,by decide⟩,⟨2018,by decide⟩,⟨3223,by decide⟩] | 2 => ![⟨3195,by decide⟩,⟨3215,by decide⟩,⟨3223,by decide⟩] | 3 => ![⟨395,by decide⟩,⟨3224,by decide⟩,⟨2047,by decide⟩] | 4 => ![⟨397,by decide⟩,⟨3225,by decide⟩,⟨397,by decide⟩] | 5 => ![⟨395,by decide⟩,⟨3226,by decide⟩,⟨2049,by decide⟩] | 6 => ![⟨397,by decide⟩,⟨3227,by decide⟩,⟨397,by decide⟩] | _ => ![⟨3228,by decide⟩,⟨3205,by decide⟩,⟨347,by decide⟩]

def ntree10RRLLRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RRLLRRLLL i else ntree10RRLLRRLLR (i - 7)

def ntree10RRLLRRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨404,by decide⟩,⟨1644,by decide⟩,⟨3229,by decide⟩] | 1 => ![⟨407,by decide⟩,⟨1646,by decide⟩,⟨3230,by decide⟩] | 2 => ![⟨3231,by decide⟩,⟨3231,by decide⟩,⟨2939,by decide⟩] | 3 => ![⟨3232,by decide⟩,⟨3233,by decide⟩,⟨3230,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨3234,by decide⟩] | 5 => ![⟨3235,by decide⟩,⟨15,by decide⟩,⟨2939,by decide⟩] | 6 => ![⟨3236,by decide⟩,⟨3236,by decide⟩,⟨2937,by decide⟩] | _ => ![⟨3102,by decide⟩,⟨3237,by decide⟩,⟨3238,by decide⟩]

def ntree10RRLLRRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3100,by decide⟩,⟨3100,by decide⟩,⟨2939,by decide⟩] | 1 => ![⟨201,by decide⟩,⟨201,by decide⟩,⟨2939,by decide⟩] | 2 => ![⟨3239,by decide⟩,⟨15,by decide⟩,⟨3239,by decide⟩] | 3 => ![⟨3240,by decide⟩,⟨3111,by decide⟩,⟨3241,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨3242,by decide⟩] | 5 => ![⟨3243,by decide⟩,⟨15,by decide⟩,⟨2939,by decide⟩] | 6 => ![⟨195,by decide⟩,⟨195,by decide⟩,⟨3244,by decide⟩] | _ => ![⟨3245,by decide⟩,⟨1637,by decide⟩,⟨2943,by decide⟩]

def ntree10RRLLRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLLRRLRL i else ntree10RRLLRRLRR (i - 8)

def ntree10RRLLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RRLLRRLL i else ntree10RRLLRRLR (i - 15)

def ntree10RRLLRRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3108,by decide⟩,⟨3108,by decide⟩,⟨2943,by decide⟩] | 1 => ![⟨201,by decide⟩,⟨3246,by decide⟩,⟨2069,by decide⟩] | 2 => ![⟨424,by decide⟩,⟨3247,by decide⟩,⟨1644,by decide⟩] | 3 => ![⟨201,by decide⟩,⟨3248,by decide⟩,⟨1646,by decide⟩] | 4 => ![⟨195,by decide⟩,⟨3249,by decide⟩,⟨195,by decide⟩] | 5 => ![⟨3250,by decide⟩,⟨3250,by decide⟩,⟨1637,by decide⟩] | 6 => ![⟨3250,by decide⟩,⟨3251,by decide⟩,⟨1650,by decide⟩] | _ => ![⟨3252,by decide⟩,⟨3252,by decide⟩,⟨1651,by decide⟩]

def ntree10RRLLRRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3108,by decide⟩,⟨3253,by decide⟩,⟨2074,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨1671,by decide⟩,⟨3254,by decide⟩] | 2 => ![⟨3255,by decide⟩,⟨2970,by decide⟩,⟨3255,by decide⟩] | 3 => ![⟨3256,by decide⟩,⟨3257,by decide⟩,⟨3258,by decide⟩] | 4 => ![⟨3255,by decide⟩,⟨15,by decide⟩,⟨3258,by decide⟩] | 5 => ![⟨2076,by decide⟩,⟨225,by decide⟩,⟨2939,by decide⟩] | 6 => ![⟨2076,by decide⟩,⟨2970,by decide⟩,⟨3259,by decide⟩] | _ => ![⟨3260,by decide⟩,⟨2962,by decide⟩,⟨3260,by decide⟩]

def ntree10RRLLRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLLRRRLL i else ntree10RRLLRRRLR (i - 8)

def ntree10RRLLRRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3261,by decide⟩,⟨3262,by decide⟩,⟨3263,by decide⟩] | 1 => ![⟨3264,by decide⟩,⟨3121,by decide⟩,⟨3258,by decide⟩] | 2 => ![⟨451,by decide⟩,⟨2971,by decide⟩,⟨451,by decide⟩] | 3 => ![⟨3265,by decide⟩,⟨3134,by decide⟩,⟨3266,by decide⟩] | 4 => ![⟨3267,by decide⟩,⟨3136,by decide⟩,⟨3254,by decide⟩] | 5 => ![⟨454,by decide⟩,⟨2971,by decide⟩,⟨3268,by decide⟩] | 6 => ![⟨3269,by decide⟩,⟨3137,by decide⟩,⟨3270,by decide⟩] | _ => ![⟨3271,by decide⟩,⟨1637,by decide⟩,⟨3271,by decide⟩]

def ntree10RRLLRRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3271,by decide⟩,⟨1637,by decide⟩,⟨3272,by decide⟩] | 1 => ![⟨2080,by decide⟩,⟨3129,by decide⟩,⟨2943,by decide⟩] | 2 => ![⟨3271,by decide⟩,⟨2972,by decide⟩,⟨3271,by decide⟩] | 3 => ![⟨3273,by decide⟩,⟨3130,by decide⟩,⟨3272,by decide⟩] | 4 => ![⟨424,by decide⟩,⟨3274,by decide⟩,⟨9,by decide⟩] | 5 => ![⟨3250,by decide⟩,⟨3275,by decide⟩,⟨1637,by decide⟩] | 6 => ![⟨3252,by decide⟩,⟨3276,by decide⟩,⟨1651,by decide⟩] | _ => ![⟨407,by decide⟩,⟨1671,by decide⟩,⟨3277,by decide⟩]

def ntree10RRLLRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLLRRRRL i else ntree10RRLLRRRRR (i - 8)

def ntree10RRLLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RRLLRRRL i else ntree10RRLLRRRR (i - 16)

def ntree10RRLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RRLLRRL i else ntree10RRLLRRR (i - 31)

def ntree10RRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10RRLLRL i else ntree10RRLLRR (i - 63)

def ntree10RRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 126 then ntree10RRLLL i else ntree10RRLLR (i - 126)

def ntree10RRLRLLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨407,by decide⟩,⟨1689,by decide⟩,⟨3278,by decide⟩] | 1 => ![⟨3279,by decide⟩,⟨3280,by decide⟩,⟨3255,by decide⟩] | 2 => ![⟨3279,by decide⟩,⟨3281,by decide⟩,⟨3258,by decide⟩] | 3 => ![⟨3282,by decide⟩,⟨3280,by decide⟩,⟨407,by decide⟩] | 4 => ![⟨3282,by decide⟩,⟨3283,by decide⟩,⟨3230,by decide⟩] | 5 => ![⟨2088,by decide⟩,⟨2088,by decide⟩,⟨3284,by decide⟩] | _ => ![⟨2087,by decide⟩,⟨3285,by decide⟩,⟨3284,by decide⟩]

def ntree10RRLRLLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3279,by decide⟩,⟨3286,by decide⟩,⟨3287,by decide⟩] | 1 => ![⟨3288,by decide⟩,⟨3289,by decide⟩,⟨3290,by decide⟩] | 2 => ![⟨3280,by decide⟩,⟨3280,by decide⟩,⟨2992,by decide⟩] | 3 => ![⟨3291,by decide⟩,⟨3291,by decide⟩,⟨2994,by decide⟩] | 4 => ![⟨265,by decide⟩,⟨3152,by decide⟩,⟨1671,by decide⟩] | 5 => ![⟨3292,by decide⟩,⟨3143,by decide⟩,⟨3293,by decide⟩] | 6 => ![⟨3255,by decide⟩,⟨1866,by decide⟩,⟨3294,by decide⟩] | _ => ![⟨2076,by decide⟩,⟨15,by decide⟩,⟨81,by decide⟩]

def ntree10RRLRLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RRLRLLLLL i else ntree10RRLRLLLLR (i - 7)

def ntree10RRLRLLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3295,by decide⟩,⟨3146,by decide⟩,⟨3294,by decide⟩] | 1 => ![⟨431,by decide⟩,⟨3296,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨431,by decide⟩,⟨3297,by decide⟩,⟨1646,by decide⟩] | 3 => ![⟨3280,by decide⟩,⟨3298,by decide⟩,⟨1866,by decide⟩] | 4 => ![⟨3280,by decide⟩,⟨3281,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨3280,by decide⟩,⟨3299,by decide⟩,⟨72,by decide⟩] | 6 => ![⟨3280,by decide⟩,⟨3283,by decide⟩,⟨1646,by decide⟩] | _ => ![⟨2088,by decide⟩,⟨3300,by decide⟩,⟨2088,by decide⟩]

def ntree10RRLRLLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2088,by decide⟩,⟨3285,by decide⟩,⟨2088,by decide⟩] | 1 => ![⟨3301,by decide⟩,⟨3302,by decide⟩,⟨2099,by decide⟩] | 2 => ![⟨3303,by decide⟩,⟨3304,by decide⟩,⟨1695,by decide⟩] | 3 => ![⟨3291,by decide⟩,⟨3289,by decide⟩,⟨2064,by decide⟩] | 4 => ![⟨3301,by decide⟩,⟨3301,by decide⟩,⟨1695,by decide⟩] | 5 => ![⟨3303,by decide⟩,⟨3303,by decide⟩,⟨1695,by decide⟩] | 6 => ![⟨3291,by decide⟩,⟨3291,by decide⟩,⟨15,by decide⟩] | _ => ![⟨3305,by decide⟩,⟨3306,by decide⟩,⟨1712,by decide⟩]

def ntree10RRLRLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLRLLLRL i else ntree10RRLRLLLRR (i - 8)

def ntree10RRLRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RRLRLLLL i else ntree10RRLRLLLR (i - 15)

def ntree10RRLRLLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3103,by decide⟩,⟨2938,by decide⟩,⟨3103,by decide⟩] | 1 => ![⟨3307,by decide⟩,⟨3307,by decide⟩,⟨9,by decide⟩] | 2 => ![⟨3158,by decide⟩,⟨3308,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨3309,by decide⟩,⟨97,by decide⟩,⟨3239,by decide⟩] | 4 => ![⟨3310,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 5 => ![⟨505,by decide⟩,⟨3311,by decide⟩,⟨1707,by decide⟩] | 6 => ![⟨282,by decide⟩,⟨3312,by decide⟩,⟨2120,by decide⟩] | _ => ![⟨3313,by decide⟩,⟨3314,by decide⟩,⟨1730,by decide⟩]

def ntree10RRLRLLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3315,by decide⟩,⟨3315,by decide⟩,⟨1651,by decide⟩] | 1 => ![⟨3160,by decide⟩,⟨3316,by decide⟩,⟨1637,by decide⟩] | 2 => ![⟨3317,by decide⟩,⟨3031,by decide⟩,⟨3318,by decide⟩] | 3 => ![⟨3317,by decide⟩,⟨97,by decide⟩,⟨3255,by decide⟩] | 4 => ![⟨3305,by decide⟩,⟨3319,by decide⟩,⟨308,by decide⟩] | 5 => ![⟨3255,by decide⟩,⟨2971,by decide⟩,⟨3255,by decide⟩] | 6 => ![⟨3307,by decide⟩,⟨3320,by decide⟩,⟨515,by decide⟩] | _ => ![⟨520,by decide⟩,⟨3028,by decide⟩,⟨3321,by decide⟩]

def ntree10RRLRLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLRLLRLL i else ntree10RRLRLLRLR (i - 8)

def ntree10RRLRLLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3322,by decide⟩,⟨3017,by decide⟩,⟨3271,by decide⟩] | 1 => ![⟨505,by decide⟩,⟨3323,by decide⟩,⟨2133,by decide⟩] | 2 => ![⟨3313,by decide⟩,⟨3324,by decide⟩,⟨1954,by decide⟩] | 3 => ![⟨3315,by decide⟩,⟨3325,by decide⟩,⟨2136,by decide⟩] | 4 => ![⟨3255,by decide⟩,⟨1712,by decide⟩,⟨3326,by decide⟩] | 5 => ![⟨3317,by decide⟩,⟨3011,by decide⟩,⟨3326,by decide⟩] | 6 => ![⟨3327,by decide⟩,⟨3327,by decide⟩,⟨2088,by decide⟩] | _ => ![⟨3327,by decide⟩,⟨3328,by decide⟩,⟨2145,by decide⟩]

def ntree10RRLRLLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3329,by decide⟩,⟨2993,by decide⟩,⟨3329,by decide⟩] | 1 => ![⟨3330,by decide⟩,⟨3331,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨3332,by decide⟩,⟨3333,by decide⟩,⟨308,by decide⟩] | 3 => ![⟨497,by decide⟩,⟨2971,by decide⟩,⟨3334,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨3335,by decide⟩] | 5 => ![⟨3336,by decide⟩,⟨15,by decide⟩,⟨3255,by decide⟩] | 6 => ![⟨3337,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | _ => ![⟨15,by decide⟩,⟨2149,by decide⟩,⟨2149,by decide⟩]

def ntree10RRLRLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLRLLRRL i else ntree10RRLRLLRRR (i - 8)

def ntree10RRLRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RRLRLLRL i else ntree10RRLRLLRR (i - 16)

def ntree10RRLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RRLRLLL i else ntree10RRLRLLR (i - 31)

def ntree10RRLRLRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨535,by decide⟩,⟨3338,by decide⟩,⟨2151,by decide⟩] | 1 => ![⟨3327,by decide⟩,⟨3339,by decide⟩,⟨2153,by decide⟩] | 2 => ![⟨3340,by decide⟩,⟨3341,by decide⟩,⟨2145,by decide⟩] | 3 => ![⟨3342,by decide⟩,⟨3343,by decide⟩,⟨1695,by decide⟩] | 4 => ![⟨3344,by decide⟩,⟨3345,by decide⟩,⟨2156,by decide⟩] | 5 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨3234,by decide⟩] | _ => ![⟨3346,by decide⟩,⟨3306,by decide⟩,⟨3048,by decide⟩]

def ntree10RRLRLRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3347,by decide⟩,⟨15,by decide⟩,⟨3348,by decide⟩] | 1 => ![⟨9,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | 2 => ![⟨3307,by decide⟩,⟨3307,by decide⟩,⟨2937,by decide⟩] | 3 => ![⟨3349,by decide⟩,⟨3308,by decide⟩,⟨3348,by decide⟩] | 4 => ![⟨3350,by decide⟩,⟨3198,by decide⟩,⟨3053,by decide⟩] | 5 => ![⟨362,by decide⟩,⟨362,by decide⟩,⟨3351,by decide⟩] | 6 => ![⟨497,by decide⟩,⟨3205,by decide⟩,⟨2939,by decide⟩] | _ => ![⟨3352,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩]

def ntree10RRLRLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RRLRLRLLL i else ntree10RRLRLRLLR (i - 7)

def ntree10RRLRLRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨3158,by decide⟩,⟨3158,by decide⟩,⟨2939,by decide⟩] | 2 => ![⟨95,by decide⟩,⟨3353,by decide⟩,⟨2068,by decide⟩] | 3 => ![⟨424,by decide⟩,⟨3354,by decide⟩,⟨1707,by decide⟩] | 4 => ![⟨362,by decide⟩,⟨3355,by decide⟩,⟨2164,by decide⟩] | 5 => ![⟨431,by decide⟩,⟨3356,by decide⟩,⟨1712,by decide⟩] | 6 => ![⟨3357,by decide⟩,⟨97,by decide⟩,⟨3358,by decide⟩] | _ => ![⟨3358,by decide⟩,⟨308,by decide⟩,⟨3359,by decide⟩]

def ntree10RRLRLRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3357,by decide⟩,⟨309,by decide⟩,⟨3359,by decide⟩] | 1 => ![⟨3357,by decide⟩,⟨3031,by decide⟩,⟨3360,by decide⟩] | 2 => ![⟨3361,by decide⟩,⟨3319,by decide⟩,⟨3359,by decide⟩] | 3 => ![⟨3362,by decide⟩,⟨9,by decide⟩,⟨3362,by decide⟩] | 4 => ![⟨3362,by decide⟩,⟨515,by decide⟩,⟨3363,by decide⟩] | 5 => ![⟨3362,by decide⟩,⟨2962,by decide⟩,⟨3362,by decide⟩] | 6 => ![⟨3364,by decide⟩,⟨3320,by decide⟩,⟨3363,by decide⟩] | _ => ![⟨3365,by decide⟩,⟨3166,by decide⟩,⟨3359,by decide⟩]

def ntree10RRLRLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLRLRLRL i else ntree10RRLRLRLRR (i - 8)

def ntree10RRLRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RRLRLRLL i else ntree10RRLRLRLR (i - 15)

def ntree10RRLRLRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3366,by decide⟩,⟨3216,by decide⟩,⟨3367,by decide⟩] | 1 => ![⟨451,by decide⟩,⟨15,by decide⟩,⟨3266,by decide⟩] | 2 => ![⟨520,by decide⟩,⟨97,by decide⟩,⟨3266,by decide⟩] | 3 => ![⟨3358,by decide⟩,⟨168,by decide⟩,⟨3358,by decide⟩] | 4 => ![⟨3368,by decide⟩,⟨389,by decide⟩,⟨3359,by decide⟩] | 5 => ![⟨3358,by decide⟩,⟨2971,by decide⟩,⟨3358,by decide⟩] | 6 => ![⟨431,by decide⟩,⟨3369,by decide⟩,⟨15,by decide⟩] | _ => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨2992,by decide⟩]

def ntree10RRLRLRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨2939,by decide⟩] | 1 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨2994,by decide⟩] | 2 => ![⟨3370,by decide⟩,⟨3327,by decide⟩,⟨3371,by decide⟩] | 3 => ![⟨3371,by decide⟩,⟨2145,by decide⟩,⟨3372,by decide⟩] | 4 => ![⟨3370,by decide⟩,⟨3328,by decide⟩,⟨3372,by decide⟩] | 5 => ![⟨3358,by decide⟩,⟨15,by decide⟩,⟨3373,by decide⟩] | 6 => ![⟨3374,by decide⟩,⟨308,by decide⟩,⟨3375,by decide⟩] | _ => ![⟨3376,by decide⟩,⟨3331,by decide⟩,⟨3373,by decide⟩]

def ntree10RRLRLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLRLRRLL i else ntree10RRLRLRRLR (i - 8)

def ntree10RRLRLRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3377,by decide⟩,⟨3333,by decide⟩,⟨3375,by decide⟩] | 1 => ![⟨3378,by decide⟩,⟨3225,by decide⟩,⟨3379,by decide⟩] | 2 => ![⟨397,by decide⟩,⟨397,by decide⟩,⟨3380,by decide⟩] | 3 => ![⟨3381,by decide⟩,⟨265,by decide⟩,⟨3358,by decide⟩] | 4 => ![⟨574,by decide⟩,⟨3382,by decide⟩,⟨2179,by decide⟩] | 5 => ![⟨578,by decide⟩,⟨2183,by decide⟩,⟨3383,by decide⟩] | 6 => ![⟨14,by decide⟩,⟨2186,by decide⟩,⟨3384,by decide⟩] | _ => ![⟨583,by decide⟩,⟨2188,by decide⟩,⟨3385,by decide⟩]

def ntree10RRLRLRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨607,by decide⟩,⟨607,by decide⟩,⟨2939,by decide⟩] | 1 => ![⟨588,by decide⟩,⟨2186,by decide⟩,⟨3386,by decide⟩] | 2 => ![⟨608,by decide⟩,⟨3387,by decide⟩,⟨2936,by decide⟩] | 3 => ![⟨3388,by decide⟩,⟨3388,by decide⟩,⟨2931,by decide⟩] | 4 => ![⟨3389,by decide⟩,⟨593,by decide⟩,⟨3390,by decide⟩] | 5 => ![⟨3391,by decide⟩,⟨3391,by decide⟩,⟨2939,by decide⟩] | 6 => ![⟨3392,by decide⟩,⟨595,by decide⟩,⟨3393,by decide⟩] | _ => ![⟨3394,by decide⟩,⟨2195,by decide⟩,⟨3395,by decide⟩]

def ntree10RRLRLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLRLRRRL i else ntree10RRLRLRRRR (i - 8)

def ntree10RRLRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RRLRLRRL i else ntree10RRLRLRRR (i - 16)

def ntree10RRLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RRLRLRL i else ntree10RRLRLRR (i - 31)

def ntree10RRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10RRLRLL i else ntree10RRLRLR (i - 63)

def ntree10RRLRRLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3396,by decide⟩,⟨2197,by decide⟩,⟨3397,by decide⟩] | 1 => ![⟨3398,by decide⟩,⟨3398,by decide⟩,⟨2943,by decide⟩] | 2 => ![⟨3391,by decide⟩,⟨3391,by decide⟩,⟨2947,by decide⟩] | 3 => ![⟨3399,by decide⟩,⟨595,by decide⟩,⟨3400,by decide⟩] | 4 => ![⟨3401,by decide⟩,⟨3402,by decide⟩,⟨2949,by decide⟩] | 5 => ![⟨3401,by decide⟩,⟨3391,by decide⟩,⟨14,by decide⟩] | _ => ![⟨3403,by decide⟩,⟨2197,by decide⟩,⟨3404,by decide⟩]

def ntree10RRLRRLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2952,by decide⟩,⟨2197,by decide⟩,⟨3405,by decide⟩] | 1 => ![⟨3398,by decide⟩,⟨3398,by decide⟩,⟨1637,by decide⟩] | 2 => ![⟨3406,by decide⟩,⟨3398,by decide⟩,⟨2952,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨3407,by decide⟩,⟨1661,by decide⟩] | 4 => ![⟨610,by decide⟩,⟨3,by decide⟩,⟨3408,by decide⟩] | 5 => ![⟨613,by decide⟩,⟨1661,by decide⟩,⟨3409,by decide⟩] | 6 => ![⟨613,by decide⟩,⟨15,by decide⟩,⟨3410,by decide⟩] | _ => ![⟨615,by decide⟩,⟨615,by decide⟩,⟨3411,by decide⟩]

def ntree10RRLRRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RRLRRLLLL i else ntree10RRLRRLLLR (i - 7)

def ntree10RRLRRLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨613,by decide⟩,⟨2971,by decide⟩,⟨613,by decide⟩] | 1 => ![⟨3412,by decide⟩,⟨3413,by decide⟩,⟨3410,by decide⟩] | 2 => ![⟨641,by decide⟩,⟨3414,by decide⟩,⟨2939,by decide⟩] | 3 => ![⟨3415,by decide⟩,⟨3407,by decide⟩,⟨3409,by decide⟩] | 4 => ![⟨3416,by decide⟩,⟨3417,by decide⟩,⟨3411,by decide⟩] | 5 => ![⟨3418,by decide⟩,⟨2958,by decide⟩,⟨3418,by decide⟩] | 6 => ![⟨3419,by decide⟩,⟨3420,by decide⟩,⟨3421,by decide⟩] | _ => ![⟨3422,by decide⟩,⟨2971,by decide⟩,⟨3422,by decide⟩]

def ntree10RRLRRLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3423,by decide⟩,⟨3424,by decide⟩,⟨3425,by decide⟩] | 1 => ![⟨3426,by decide⟩,⟨1635,by decide⟩,⟨3426,by decide⟩] | 2 => ![⟨3426,by decide⟩,⟨1635,by decide⟩,⟨3427,by decide⟩] | 3 => ![⟨3428,by decide⟩,⟨1637,by decide⟩,⟨3428,by decide⟩] | 4 => ![⟨3428,by decide⟩,⟨1637,by decide⟩,⟨3429,by decide⟩] | 5 => ![⟨3428,by decide⟩,⟨2972,by decide⟩,⟨3428,by decide⟩] | 6 => ![⟨3430,by decide⟩,⟨3431,by decide⟩,⟨3429,by decide⟩] | _ => ![⟨3432,by decide⟩,⟨2971,by decide⟩,⟨3432,by decide⟩]

def ntree10RRLRRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLRRLLRL i else ntree10RRLRRLLRR (i - 8)

def ntree10RRLRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RRLRRLLL i else ntree10RRLRRLLR (i - 15)

def ntree10RRLRRLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3433,by decide⟩,⟨3424,by decide⟩,⟨3434,by decide⟩] | 1 => ![⟨2211,by decide⟩,⟨3435,by decide⟩,⟨2947,by decide⟩] | 2 => ![⟨2211,by decide⟩,⟨2971,by decide⟩,⟨637,by decide⟩] | 3 => ![⟨3391,by decide⟩,⟨3424,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨3436,by decide⟩,⟨1637,by decide⟩,⟨3436,by decide⟩] | 5 => ![⟨3436,by decide⟩,⟨1637,by decide⟩,⟨3437,by decide⟩] | 6 => ![⟨1637,by decide⟩,⟨1637,by decide⟩,⟨3438,by decide⟩] | _ => ![⟨3398,by decide⟩,⟨3431,by decide⟩,⟨1637,by decide⟩]

def ntree10RRLRRLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2215,by decide⟩,⟨2972,by decide⟩,⟨3438,by decide⟩] | 1 => ![⟨645,by decide⟩,⟨2219,by decide⟩,⟨3439,by decide⟩] | 2 => ![⟨645,by decide⟩,⟨3440,by decide⟩,⟨645,by decide⟩] | 3 => ![⟨3441,by decide⟩,⟨3442,by decide⟩,⟨3439,by decide⟩] | 4 => ![⟨3443,by decide⟩,⟨3444,by decide⟩,⟨593,by decide⟩] | 5 => ![⟨3445,by decide⟩,⟨3444,by decide⟩,⟨3390,by decide⟩] | 6 => ![⟨3443,by decide⟩,⟨3443,by decide⟩,⟨3,by decide⟩] | _ => ![⟨3443,by decide⟩,⟨3443,by decide⟩,⟨2931,by decide⟩]

def ntree10RRLRRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLRRLRLL i else ntree10RRLRRLRLR (i - 8)

def ntree10RRLRRLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3446,by decide⟩,⟨3447,by decide⟩,⟨595,by decide⟩] | 1 => ![⟨3448,by decide⟩,⟨3447,by decide⟩,⟨3393,by decide⟩] | 2 => ![⟨3449,by decide⟩,⟨3447,by decide⟩,⟨657,by decide⟩] | 3 => ![⟨3446,by decide⟩,⟨3446,by decide⟩,⟨81,by decide⟩] | 4 => ![⟨3446,by decide⟩,⟨3446,by decide⟩,⟨2939,by decide⟩] | 5 => ![⟨3450,by decide⟩,⟨3447,by decide⟩,⟨3400,by decide⟩] | 6 => ![⟨3451,by decide⟩,⟨3446,by decide⟩,⟨14,by decide⟩] | _ => ![⟨3451,by decide⟩,⟨3452,by decide⟩,⟨2949,by decide⟩]

def ntree10RRLRRLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3451,by decide⟩,⟨3447,by decide⟩,⟨603,by decide⟩] | 1 => ![⟨634,by decide⟩,⟨15,by decide⟩,⟨3453,by decide⟩] | 2 => ![⟨607,by decide⟩,⟨3413,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨608,by decide⟩,⟨3413,by decide⟩,⟨14,by decide⟩] | 4 => ![⟨578,by decide⟩,⟨1699,by decide⟩,⟨3454,by decide⟩] | 5 => ![⟨583,by decide⟩,⟨2235,by decide⟩,⟨3455,by decide⟩] | 6 => ![⟨3456,by decide⟩,⟨3456,by decide⟩,⟨15,by decide⟩] | _ => ![⟨588,by decide⟩,⟨1715,by decide⟩,⟨3457,by decide⟩]

def ntree10RRLRRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLRRLRRL i else ntree10RRLRRLRRR (i - 8)

def ntree10RRLRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RRLRRLRL i else ntree10RRLRRLRR (i - 16)

def ntree10RRLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RRLRRLL i else ntree10RRLRRLR (i - 31)

def ntree10RRLRRRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3458,by decide⟩,⟨3456,by decide⟩,⟨14,by decide⟩] | 1 => ![⟨3389,by decide⟩,⟨3,by decide⟩,⟨3389,by decide⟩] | 2 => ![⟨3459,by decide⟩,⟨3459,by decide⟩,⟨3015,by decide⟩] | 3 => ![⟨3392,by decide⟩,⟨15,by decide⟩,⟨3460,by decide⟩] | 4 => ![⟨3394,by decide⟩,⟨1635,by decide⟩,⟨3394,by decide⟩] | 5 => ![⟨3396,by decide⟩,⟨1637,by decide⟩,⟨3461,by decide⟩] | _ => ![⟨3396,by decide⟩,⟨1637,by decide⟩,⟨3396,by decide⟩]

def ntree10RRLRRRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3399,by decide⟩,⟨1712,by decide⟩,⟨3462,by decide⟩] | 1 => ![⟨3403,by decide⟩,⟨1730,by decide⟩,⟨3463,by decide⟩] | 2 => ![⟨671,by decide⟩,⟨3464,by decide⟩,⟨1743,by decide⟩] | 3 => ![⟨674,by decide⟩,⟨3465,by decide⟩,⟨1745,by decide⟩] | 4 => ![⟨610,by decide⟩,⟨1743,by decide⟩,⟨3466,by decide⟩] | 5 => ![⟨613,by decide⟩,⟨1745,by decide⟩,⟨3467,by decide⟩] | 6 => ![⟨613,by decide⟩,⟨2263,by decide⟩,⟨3468,by decide⟩] | _ => ![⟨615,by decide⟩,⟨615,by decide⟩,⟨3469,by decide⟩]

def ntree10RRLRRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RRLRRRLLL i else ntree10RRLRRRLLR (i - 7)

def ntree10RRLRRRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3470,by decide⟩,⟨3471,by decide⟩,⟨3472,by decide⟩] | 1 => ![⟨3473,by decide⟩,⟨2971,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨3474,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨615,by decide⟩,⟨3475,by decide⟩,⟨615,by decide⟩] | 4 => ![⟨3476,by decide⟩,⟨3477,by decide⟩,⟨3478,by decide⟩] | 5 => ![⟨3428,by decide⟩,⟨2271,by decide⟩,⟨3479,by decide⟩] | 6 => ![⟨3480,by decide⟩,⟨3465,by decide⟩,⟨3481,by decide⟩] | _ => ![⟨3482,by decide⟩,⟨2971,by decide⟩,⟨15,by decide⟩]

def ntree10RRLRRRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨3483,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨3436,by decide⟩,⟨1754,by decide⟩,⟨3484,by decide⟩] | 2 => ![⟨3485,by decide⟩,⟨2972,by decide⟩,⟨1637,by decide⟩] | 3 => ![⟨610,by decide⟩,⟨1699,by decide⟩,⟨3486,by decide⟩] | 4 => ![⟨7,by decide⟩,⟨2261,by decide⟩,⟨3487,by decide⟩] | 5 => ![⟨645,by decide⟩,⟨2282,by decide⟩,⟨3488,by decide⟩] | 6 => ![⟨3489,by decide⟩,⟨3042,by decide⟩,⟨3490,by decide⟩] | _ => ![⟨14,by decide⟩,⟨2266,by decide⟩,⟨3491,by decide⟩]

def ntree10RRLRRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLRRRLRL i else ntree10RRLRRRLRR (i - 8)

def ntree10RRLRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RRLRRRLL i else ntree10RRLRRRLR (i - 15)

def ntree10RRLRRRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3389,by decide⟩,⟨2958,by decide⟩,⟨3389,by decide⟩] | 1 => ![⟨3,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 2 => ![⟨3492,by decide⟩,⟨3493,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨3494,by decide⟩,⟨3493,by decide⟩,⟨3460,by decide⟩] | 4 => ![⟨3392,by decide⟩,⟨2971,by decide⟩,⟨3392,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨3495,by decide⟩,⟨3039,by decide⟩,⟨3462,by decide⟩] | _ => ![⟨14,by decide⟩,⟨3483,by decide⟩,⟨14,by decide⟩]

def ntree10RRLRRRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨634,by decide⟩,⟨1712,by decide⟩,⟨3496,by decide⟩] | 1 => ![⟨707,by decide⟩,⟨2971,by decide⟩,⟨3497,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨2296,by decide⟩,⟨2296,by decide⟩] | 3 => ![⟨753,by decide⟩,⟨2298,by decide⟩,⟨3498,by decide⟩] | 4 => ![⟨755,by decide⟩,⟨2300,by decide⟩,⟨3499,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨3500,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨707,by decide⟩,⟨3501,by decide⟩,⟨2939,by decide⟩] | _ => ![⟨759,by decide⟩,⟨759,by decide⟩,⟨3502,by decide⟩]

def ntree10RRLRRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLRRRRLL i else ntree10RRLRRRRLR (i - 8)

def ntree10RRLRRRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3503,by decide⟩,⟨15,by decide⟩,⟨3504,by decide⟩] | 1 => ![⟨3505,by decide⟩,⟨3505,by decide⟩,⟨3055,by decide⟩] | 2 => ![⟨3506,by decide⟩,⟨595,by decide⟩,⟨3507,by decide⟩] | 3 => ![⟨3508,by decide⟩,⟨2302,by decide⟩,⟨3509,by decide⟩] | 4 => ![⟨3510,by decide⟩,⟨1802,by decide⟩,⟨3511,by decide⟩] | 5 => ![⟨765,by decide⟩,⟨15,by decide⟩,⟨3512,by decide⟩] | 6 => ![⟨3391,by decide⟩,⟨3513,by decide⟩,⟨1712,by decide⟩] | _ => ![⟨3514,by decide⟩,⟨2307,by decide⟩,⟨3514,by decide⟩]

def ntree10RRLRRRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3401,by decide⟩,⟨3513,by decide⟩,⟨3012,by decide⟩] | 1 => ![⟨3514,by decide⟩,⟨2308,by decide⟩,⟨3515,by decide⟩] | 2 => ![⟨3516,by decide⟩,⟨2308,by decide⟩,⟨3517,by decide⟩] | 3 => ![⟨3514,by decide⟩,⟨2317,by decide⟩,⟨3518,by decide⟩] | 4 => ![⟨3519,by decide⟩,⟨3391,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨674,by decide⟩,⟨3520,by decide⟩,⟨1661,by decide⟩] | 6 => ![⟨674,by decide⟩,⟨3521,by decide⟩,⟨1821,by decide⟩] | _ => ![⟨634,by decide⟩,⟨1745,by decide⟩,⟨3522,by decide⟩]

def ntree10RRLRRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRLRRRRRL i else ntree10RRLRRRRRR (i - 8)

def ntree10RRLRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RRLRRRRL i else ntree10RRLRRRRR (i - 16)

def ntree10RRLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RRLRRRL i else ntree10RRLRRRR (i - 31)

def ntree10RRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10RRLRRL i else ntree10RRLRRR (i - 63)

def ntree10RRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 126 then ntree10RRLRL i else ntree10RRLRR (i - 126)

def ntree10RRL (i : Nat) : Fin 3 → Fin 3959 := if i < 252 then ntree10RRLL i else ntree10RRLR (i - 252)

def ntree10RRRLLLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨634,by decide⟩,⟨15,by decide⟩,⟨3523,by decide⟩] | 1 => ![⟨772,by decide⟩,⟨1661,by decide⟩,⟨3524,by decide⟩] | 2 => ![⟨772,by decide⟩,⟨2266,by decide⟩,⟨3525,by decide⟩] | 3 => ![⟨3526,by decide⟩,⟨3527,by decide⟩,⟨3502,by decide⟩] | 4 => ![⟨3528,by decide⟩,⟨3076,by decide⟩,⟨3528,by decide⟩] | 5 => ![⟨3529,by decide⟩,⟨3530,by decide⟩,⟨3531,by decide⟩] | _ => ![⟨3532,by decide⟩,⟨3077,by decide⟩,⟨3532,by decide⟩]

def ntree10RRRLLLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3533,by decide⟩,⟨3534,by decide⟩,⟨3535,by decide⟩] | 1 => ![⟨3536,by decide⟩,⟨1802,by decide⟩,⟨3536,by decide⟩] | 2 => ![⟨3536,by decide⟩,⟨1802,by decide⟩,⟨3537,by decide⟩] | 3 => ![⟨3538,by decide⟩,⟨1802,by decide⟩,⟨3538,by decide⟩] | 4 => ![⟨3538,by decide⟩,⟨2327,by decide⟩,⟨3539,by decide⟩] | 5 => ![⟨3532,by decide⟩,⟨15,by decide⟩,⟨3532,by decide⟩] | 6 => ![⟨3532,by decide⟩,⟨2268,by decide⟩,⟨3535,by decide⟩] | _ => ![⟨3540,by decide⟩,⟨3541,by decide⟩,⟨3525,by decide⟩]

def ntree10RRRLLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RRRLLLLLL i else ntree10RRRLLLLLR (i - 7)

def ntree10RRRLLLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2307,by decide⟩,⟨3542,by decide⟩,⟨2307,by decide⟩] | 1 => ![⟨3543,by decide⟩,⟨674,by decide⟩,⟨3528,by decide⟩] | 2 => ![⟨3529,by decide⟩,⟨3391,by decide⟩,⟨3528,by decide⟩] | 3 => ![⟨3543,by decide⟩,⟨3465,by decide⟩,⟨3544,by decide⟩] | 4 => ![⟨3529,by decide⟩,⟨3424,by decide⟩,⟨3545,by decide⟩] | 5 => ![⟨2332,by decide⟩,⟨3542,by decide⟩,⟨3546,by decide⟩] | 6 => ![⟨2307,by decide⟩,⟨2307,by decide⟩,⟨3547,by decide⟩] | _ => ![⟨3528,by decide⟩,⟨72,by decide⟩,⟨3548,by decide⟩]

def ntree10RRRLLLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3528,by decide⟩,⟨2266,by decide⟩,⟨3549,by decide⟩] | 1 => ![⟨3528,by decide⟩,⟨1745,by decide⟩,⟨3544,by decide⟩] | 2 => ![⟨3528,by decide⟩,⟨15,by decide⟩,⟨3545,by decide⟩] | 3 => ![⟨2307,by decide⟩,⟨2307,by decide⟩,⟨3546,by decide⟩] | 4 => ![⟨2211,by decide⟩,⟨168,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨3391,by decide⟩,⟨3541,by decide⟩,⟨2266,by decide⟩] | 6 => ![⟨793,by decide⟩,⟨2340,by decide⟩,⟨3550,by decide⟩] | _ => ![⟨797,by decide⟩,⟨2343,by decide⟩,⟨3551,by decide⟩]

def ntree10RRRLLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRLLLLRL i else ntree10RRRLLLLRR (i - 8)

def ntree10RRRLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RRRLLLLL i else ntree10RRRLLLLR (i - 15)

def ntree10RRRLLLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨794,by decide⟩,⟨3552,by decide⟩,⟨794,by decide⟩] | 1 => ![⟨3553,by decide⟩,⟨3554,by decide⟩,⟨3555,by decide⟩] | 2 => ![⟨3446,by decide⟩,⟨3556,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨3557,by decide⟩,⟨3556,by decide⟩,⟨3504,by decide⟩] | 4 => ![⟨3558,by decide⟩,⟨3559,by decide⟩,⟨595,by decide⟩] | 5 => ![⟨3560,by decide⟩,⟨3559,by decide⟩,⟨3507,by decide⟩] | 6 => ![⟨3561,by decide⟩,⟨3446,by decide⟩,⟨772,by decide⟩] | _ => ![⟨3562,by decide⟩,⟨3563,by decide⟩,⟨2308,by decide⟩]

def ntree10RRRLLLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3564,by decide⟩,⟨3562,by decide⟩,⟨3514,by decide⟩] | 1 => ![⟨3564,by decide⟩,⟨3563,by decide⟩,⟨3515,by decide⟩] | 2 => ![⟨3565,by decide⟩,⟨2347,by decide⟩,⟨3565,by decide⟩] | 3 => ![⟨3566,by decide⟩,⟨2349,by decide⟩,⟨3566,by decide⟩] | 4 => ![⟨3566,by decide⟩,⟨2354,by decide⟩,⟨3567,by decide⟩] | 5 => ![⟨3568,by decide⟩,⟨3568,by decide⟩,⟨2355,by decide⟩] | 6 => ![⟨3100,by decide⟩,⟨3569,by decide⟩,⟨2186,by decide⟩] | _ => ![⟨3570,by decide⟩,⟨2355,by decide⟩,⟨3570,by decide⟩]

def ntree10RRRLLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRLLLRLL i else ntree10RRRLLLRLR (i - 8)

def ntree10RRRLLLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3571,by decide⟩,⟨3568,by decide⟩,⟨3570,by decide⟩] | 1 => ![⟨3572,by decide⟩,⟨3572,by decide⟩,⟨2347,by decide⟩] | 2 => ![⟨3573,by decide⟩,⟨3573,by decide⟩,⟨2349,by decide⟩] | 3 => ![⟨3574,by decide⟩,⟨3574,by decide⟩,⟨2365,by decide⟩] | 4 => ![⟨3108,by decide⟩,⟨3575,by decide⟩,⟨2197,by decide⟩] | 5 => ![⟨3576,by decide⟩,⟨3576,by decide⟩,⟨2355,by decide⟩] | 6 => ![⟨3577,by decide⟩,⟨3576,by decide⟩,⟨3570,by decide⟩] | _ => ![⟨3578,by decide⟩,⟨2365,by decide⟩,⟨3578,by decide⟩]

def ntree10RRRLLLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3579,by decide⟩,⟨3574,by decide⟩,⟨3578,by decide⟩] | 1 => ![⟨2347,by decide⟩,⟨3580,by decide⟩,⟨2347,by decide⟩] | 2 => ![⟨2349,by decide⟩,⟨3581,by decide⟩,⟨2349,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨2971,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨2349,by decide⟩,⟨2349,by decide⟩,⟨3582,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨3583,by decide⟩] | 6 => ![⟨2355,by decide⟩,⟨3584,by decide⟩,⟨2355,by decide⟩] | _ => ![⟨3568,by decide⟩,⟨3585,by decide⟩,⟨2355,by decide⟩]

def ntree10RRRLLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRLLLRRL i else ntree10RRRLLLRRR (i - 8)

def ntree10RRRLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RRRLLLRL i else ntree10RRRLLLRR (i - 16)

def ntree10RRRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RRRLLLL i else ntree10RRRLLLR (i - 31)

def ntree10RRRLLRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3586,by decide⟩,⟨3100,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨641,by decide⟩,⟨2971,by decide⟩,⟨3583,by decide⟩] | 2 => ![⟨3572,by decide⟩,⟨3587,by decide⟩,⟨2347,by decide⟩] | 3 => ![⟨3573,by decide⟩,⟨3588,by decide⟩,⟨2349,by decide⟩] | 4 => ![⟨2365,by decide⟩,⟨3589,by decide⟩,⟨2365,by decide⟩] | 5 => ![⟨3574,by decide⟩,⟨3590,by decide⟩,⟨2365,by decide⟩] | _ => ![⟨3576,by decide⟩,⟨3591,by decide⟩,⟨2355,by decide⟩]

def ntree10RRRLLRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3592,by decide⟩,⟨201,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨3593,by decide⟩,⟨3108,by decide⟩,⟨1637,by decide⟩] | 2 => ![⟨3566,by decide⟩,⟨3581,by decide⟩,⟨3566,by decide⟩] | 3 => ![⟨3594,by decide⟩,⟨3595,by decide⟩,⟨2359,by decide⟩] | 4 => ![⟨3594,by decide⟩,⟨3594,by decide⟩,⟨2347,by decide⟩] | 5 => ![⟨3596,by decide⟩,⟨3597,by decide⟩,⟨2360,by decide⟩] | 6 => ![⟨3598,by decide⟩,⟨3599,by decide⟩,⟨2367,by decide⟩] | _ => ![⟨3600,by decide⟩,⟨3601,by decide⟩,⟨595,by decide⟩]

def ntree10RRRLLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RRRLLRLLL i else ntree10RRRLLRLLR (i - 7)

def ntree10RRRLLRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3598,by decide⟩,⟨3598,by decide⟩,⟨2355,by decide⟩] | 1 => ![⟨3600,by decide⟩,⟨3600,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨3602,by decide⟩,⟨3598,by decide⟩,⟨3570,by decide⟩] | 3 => ![⟨3603,by decide⟩,⟨3600,by decide⟩,⟨14,by decide⟩] | 4 => ![⟨1918,by decide⟩,⟨811,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨3604,by decide⟩,⟨3604,by decide⟩,⟨2349,by decide⟩] | 6 => ![⟨1637,by decide⟩,⟨3605,by decide⟩,⟨1637,by decide⟩] | _ => ![⟨1940,by decide⟩,⟨3605,by decide⟩,⟨1637,by decide⟩]

def ntree10RRRLLRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3606,by decide⟩,⟨3584,by decide⟩,⟨2355,by decide⟩] | 1 => ![⟨3604,by decide⟩,⟨3607,by decide⟩,⟨2411,by decide⟩] | 2 => ![⟨3608,by decide⟩,⟨3584,by decide⟩,⟨2355,by decide⟩] | 3 => ![⟨3609,by decide⟩,⟨3589,by decide⟩,⟨2365,by decide⟩] | 4 => ![⟨2347,by decide⟩,⟨2347,by decide⟩,⟨3610,by decide⟩] | 5 => ![⟨3565,by decide⟩,⟨2406,by decide⟩,⟨3611,by decide⟩] | 6 => ![⟨3566,by decide⟩,⟨2407,by decide⟩,⟨3612,by decide⟩] | _ => ![⟨2393,by decide⟩,⟨3584,by decide⟩,⟨3613,by decide⟩]

def ntree10RRRLLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRLLRLRL i else ntree10RRRLLRLRR (i - 8)

def ntree10RRRLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RRRLLRLL i else ntree10RRRLLRLR (i - 15)

def ntree10RRRLLRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3570,by decide⟩,⟨2409,by decide⟩,⟨3614,by decide⟩] | 1 => ![⟨3615,by decide⟩,⟨3616,by decide⟩,⟨2349,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨3617,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨2355,by decide⟩,⟨2355,by decide⟩,⟨3613,by decide⟩] | 4 => ![⟨3618,by decide⟩,⟨3617,by decide⟩,⟨347,by decide⟩] | 5 => ![⟨2355,by decide⟩,⟨2435,by decide⟩,⟨2435,by decide⟩] | 6 => ![⟨3505,by decide⟩,⟨3505,by decide⟩,⟨15,by decide⟩] | _ => ![⟨201,by decide⟩,⟨3619,by decide⟩,⟨15,by decide⟩]

def ntree10RRRLLRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3620,by decide⟩,⟨3620,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨3158,by decide⟩,⟨3621,by decide⟩,⟨595,by decide⟩] | 2 => ![⟨3622,by decide⟩,⟨3576,by decide⟩,⟨2355,by decide⟩] | 3 => ![⟨3206,by decide⟩,⟨828,by decide⟩,⟨595,by decide⟩] | 4 => ![⟨214,by decide⟩,⟨3619,by decide⟩,⟨14,by decide⟩] | 5 => ![⟨3623,by decide⟩,⟨3620,by decide⟩,⟨14,by decide⟩] | 6 => ![⟨3157,by decide⟩,⟨3621,by decide⟩,⟨603,by decide⟩] | _ => ![⟨3624,by decide⟩,⟨2971,by decide⟩,⟨3625,by decide⟩]

def ntree10RRRLLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRLLRRLL i else ntree10RRRLLRRLR (i - 8)

def ntree10RRRLLRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2355,by decide⟩,⟨3626,by decide⟩,⟨2355,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨3076,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨3627,by decide⟩,⟨15,by decide⟩,⟨3628,by decide⟩] | 3 => ![⟨3576,by decide⟩,⟨3629,by decide⟩,⟨2451,by decide⟩] | 4 => ![⟨3505,by decide⟩,⟨3534,by decide⟩,⟨2268,by decide⟩] | 5 => ![⟨2355,by decide⟩,⟨3630,by decide⟩,⟨2355,by decide⟩] | 6 => ![⟨3576,by decide⟩,⟨3631,by decide⟩,⟨2409,by decide⟩] | _ => ![⟨15,by decide⟩,⟨3632,by decide⟩,⟨15,by decide⟩]

def ntree10RRRLLRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3620,by decide⟩,⟨3633,by decide⟩,⟨308,by decide⟩] | 1 => ![⟨3634,by decide⟩,⟨15,by decide⟩,⟨958,by decide⟩] | 2 => ![⟨3635,by decide⟩,⟨3134,by decide⟩,⟨958,by decide⟩] | 3 => ![⟨2376,by decide⟩,⟨3630,by decide⟩,⟨2355,by decide⟩] | 4 => ![⟨3592,by decide⟩,⟨389,by decide⟩,⟨308,by decide⟩] | 5 => ![⟨3636,by decide⟩,⟨3632,by decide⟩,⟨637,by decide⟩] | 6 => ![⟨3637,by decide⟩,⟨3166,by decide⟩,⟨960,by decide⟩] | _ => ![⟨2355,by decide⟩,⟨3584,by decide⟩,⟨2355,by decide⟩]

def ntree10RRRLLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRLLRRRL i else ntree10RRRLLRRRR (i - 8)

def ntree10RRRLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RRRLLRRL i else ntree10RRRLLRRR (i - 16)

def ntree10RRRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RRRLLRL i else ntree10RRRLLRR (i - 31)

def ntree10RRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10RRRLLL i else ntree10RRRLLR (i - 63)

def ntree10RRRLRLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3570,by decide⟩,⟨3626,by decide⟩,⟨3570,by decide⟩] | 1 => ![⟨3598,by decide⟩,⟨3638,by decide⟩,⟨2355,by decide⟩] | 2 => ![⟨3446,by decide⟩,⟨3639,by decide⟩,⟨308,by decide⟩] | 3 => ![⟨3640,by decide⟩,⟨3641,by decide⟩,⟨979,by decide⟩] | 4 => ![⟨3642,by decide⟩,⟨3447,by decide⟩,⟨985,by decide⟩] | 5 => ![⟨3451,by decide⟩,⟨3639,by decide⟩,⟨331,by decide⟩] | _ => ![⟨3643,by decide⟩,⟨3641,by decide⟩,⟨987,by decide⟩]

def ntree10RRRLRLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2355,by decide⟩,⟨2355,by decide⟩,⟨3644,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨811,by decide⟩,⟨2939,by decide⟩] | 2 => ![⟨3645,by decide⟩,⟨2355,by decide⟩,⟨3645,by decide⟩] | 3 => ![⟨3645,by decide⟩,⟨2467,by decide⟩,⟨3646,by decide⟩] | 4 => ![⟨3647,by decide⟩,⟨15,by decide⟩,⟨3647,by decide⟩] | 5 => ![⟨3647,by decide⟩,⟨1003,by decide⟩,⟨3648,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨2939,by decide⟩] | _ => ![⟨3647,by decide⟩,⟨2186,by decide⟩,⟨3649,by decide⟩]

def ntree10RRRLRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RRRLRLLLL i else ntree10RRRLRLLLR (i - 7)

def ntree10RRRLRLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3568,by decide⟩,⟨3568,by decide⟩,⟨3644,by decide⟩] | 1 => ![⟨3650,by decide⟩,⟨3569,by decide⟩,⟨3386,by decide⟩] | 2 => ![⟨3576,by decide⟩,⟨3576,by decide⟩,⟨3644,by decide⟩] | 3 => ![⟨3651,by decide⟩,⟨828,by decide⟩,⟨3393,by decide⟩] | 4 => ![⟨2365,by decide⟩,⟨2365,by decide⟩,⟨3652,by decide⟩] | 5 => ![⟨3574,by decide⟩,⟨3574,by decide⟩,⟨3652,by decide⟩] | 6 => ![⟨3653,by decide⟩,⟨3575,by decide⟩,⟨3397,by decide⟩] | _ => ![⟨3576,by decide⟩,⟨3654,by decide⟩,⟨2467,by decide⟩]

def ntree10RRRLRLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3391,by decide⟩,⟨3655,by decide⟩,⟨1003,by decide⟩] | 1 => ![⟨3656,by decide⟩,⟨3584,by decide⟩,⟨3644,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨1028,by decide⟩,⟨3657,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨3658,by decide⟩,⟨1028,by decide⟩] | 4 => ![⟨2963,by decide⟩,⟨3658,by decide⟩,⟨3657,by decide⟩] | 5 => ![⟨3659,by decide⟩,⟨2355,by decide⟩,⟨3659,by decide⟩] | 6 => ![⟨3659,by decide⟩,⟨2355,by decide⟩,⟨3660,by decide⟩] | _ => ![⟨613,by decide⟩,⟨1028,by decide⟩,⟨3661,by decide⟩]

def ntree10RRRLRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRLRLLRL i else ntree10RRRLRLLRR (i - 8)

def ntree10RRRLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RRRLRLLL i else ntree10RRRLRLLR (i - 15)

def ntree10RRRLRLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3659,by decide⟩,⟨3584,by decide⟩,⟨3659,by decide⟩] | 1 => ![⟨3662,by decide⟩,⟨3585,by decide⟩,⟨3660,by decide⟩] | 2 => ![⟨3663,by decide⟩,⟨3584,by decide⟩,⟨3663,by decide⟩] | 3 => ![⟨3664,by decide⟩,⟨3591,by decide⟩,⟨3665,by decide⟩] | 4 => ![⟨3666,by decide⟩,⟨2365,by decide⟩,⟨3666,by decide⟩] | 5 => ![⟨3666,by decide⟩,⟨2365,by decide⟩,⟨3667,by decide⟩] | 6 => ![⟨3666,by decide⟩,⟨3589,by decide⟩,⟨3666,by decide⟩] | _ => ![⟨3668,by decide⟩,⟨3590,by decide⟩,⟨3667,by decide⟩]

def ntree10RRRLRLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨201,by decide⟩,⟨3669,by decide⟩,⟨1028,by decide⟩] | 1 => ![⟨3647,by decide⟩,⟨2971,by decide⟩,⟨3647,by decide⟩] | 2 => ![⟨3670,by decide⟩,⟨3671,by decide⟩,⟨3648,by decide⟩] | 3 => ![⟨3672,by decide⟩,⟨2088,by decide⟩,⟨3672,by decide⟩] | 4 => ![⟨3672,by decide⟩,⟨2483,by decide⟩,⟨3673,by decide⟩] | 5 => ![⟨3659,by decide⟩,⟨2367,by decide⟩,⟨3674,by decide⟩] | 6 => ![⟨3675,by decide⟩,⟨595,by decide⟩,⟨3676,by decide⟩] | _ => ![⟨2355,by decide⟩,⟨2355,by decide⟩,⟨3677,by decide⟩]

def ntree10RRRLRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRLRLRLL i else ntree10RRRLRLRLR (i - 8)

def ntree10RRRLRLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨3678,by decide⟩] | 1 => ![⟨3679,by decide⟩,⟨3599,by decide⟩,⟨3674,by decide⟩] | 2 => ![⟨3680,by decide⟩,⟨3601,by decide⟩,⟨3676,by decide⟩] | 3 => ![⟨3598,by decide⟩,⟨3598,by decide⟩,⟨3677,by decide⟩] | 4 => ![⟨3600,by decide⟩,⟨3600,by decide⟩,⟨3678,by decide⟩] | 5 => ![⟨3446,by decide⟩,⟨3452,by decide⟩,⟨1646,by decide⟩] | 6 => ![⟨3681,by decide⟩,⟨3671,by decide⟩,⟨1003,by decide⟩] | _ => ![⟨3682,by decide⟩,⟨3682,by decide⟩,⟨2355,by decide⟩]

def ntree10RRRLRLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3683,by decide⟩,⟨3684,by decide⟩,⟨1712,by decide⟩] | 1 => ![⟨3685,by decide⟩,⟨3682,by decide⟩,⟨3645,by decide⟩] | 2 => ![⟨3686,by decide⟩,⟨3683,by decide⟩,⟨407,by decide⟩] | 3 => ![⟨3687,by decide⟩,⟨674,by decide⟩,⟨3647,by decide⟩] | 4 => ![⟨3647,by decide⟩,⟨1712,by decide⟩,⟨3688,by decide⟩] | 5 => ![⟨3689,by decide⟩,⟨1712,by decide⟩,⟨1712,by decide⟩] | 6 => ![⟨588,by decide⟩,⟨1712,by decide⟩,⟨3690,by decide⟩] | _ => ![⟨3691,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩]

def ntree10RRRLRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRLRLRRL i else ntree10RRRLRLRRR (i - 8)

def ntree10RRRLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RRRLRLRL i else ntree10RRRLRLRR (i - 16)

def ntree10RRRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RRRLRLL i else ntree10RRRLRLR (i - 31)

def ntree10RRRLRRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3692,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨3693,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨3158,by decide⟩,⟨3158,by decide⟩,⟨1062,by decide⟩] | 3 => ![⟨3694,by decide⟩,⟨3158,by decide⟩,⟨588,by decide⟩] | 4 => ![⟨3392,by decide⟩,⟨811,by decide⟩,⟨3392,by decide⟩] | 5 => ![⟨3695,by decide⟩,⟨281,by decide⟩,⟨3392,by decide⟩] | _ => ![⟨1637,by decide⟩,⟨1637,by decide⟩,⟨3696,by decide⟩]

def ntree10RRRLRRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3396,by decide⟩,⟨3605,by decide⟩,⟨3396,by decide⟩] | 1 => ![⟨3697,by decide⟩,⟨2365,by decide⟩,⟨2365,by decide⟩] | 2 => ![⟨3698,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 3 => ![⟨3699,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 4 => ![⟨3160,by decide⟩,⟨3160,by decide⟩,⟨3696,by decide⟩] | 5 => ![⟨3700,by decide⟩,⟨3160,by decide⟩,⟨3396,by decide⟩] | 6 => ![⟨3683,by decide⟩,⟨3683,by decide⟩,⟨15,by decide⟩] | _ => ![⟨281,by decide⟩,⟨3701,by decide⟩,⟨1712,by decide⟩]

def ntree10RRRLRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RRRLRRLLL i else ntree10RRRLRRLLR (i - 7)

def ntree10RRRLRRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3682,by decide⟩,⟨3702,by decide⟩,⟨2513,by decide⟩] | 1 => ![⟨3683,by decide⟩,⟨3703,by decide⟩,⟨1084,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨2971,by decide⟩,⟨1062,by decide⟩] | 3 => ![⟨3659,by decide⟩,⟨2513,by decide⟩,⟨3704,by decide⟩] | 4 => ![⟨3255,by decide⟩,⟨1084,by decide⟩,⟨3705,by decide⟩] | 5 => ![⟨3706,by decide⟩,⟨3166,by decide⟩,⟨1089,by decide⟩] | 6 => ![⟨3707,by decide⟩,⟨3168,by decide⟩,⟨3708,by decide⟩] | _ => ![⟨3428,by decide⟩,⟨1954,by decide⟩,⟨3709,by decide⟩]

def ntree10RRRLRRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3710,by decide⟩,⟨3173,by decide⟩,⟨3709,by decide⟩] | 1 => ![⟨3683,by decide⟩,⟨3711,by decide⟩,⟨1948,by decide⟩] | 2 => ![⟨2355,by decide⟩,⟨3712,by decide⟩,⟨2488,by decide⟩] | 3 => ![⟨3647,by decide⟩,⟨3039,by decide⟩,⟨3688,by decide⟩] | 4 => ![⟨3659,by decide⟩,⟨2488,by decide⟩,⟨3713,by decide⟩] | 5 => ![⟨3645,by decide⟩,⟨2409,by decide⟩,⟨3714,by decide⟩] | 6 => ![⟨3672,by decide⟩,⟨2145,by decide⟩,⟨3715,by decide⟩] | _ => ![⟨3675,by decide⟩,⟨15,by decide⟩,⟨3675,by decide⟩]

def ntree10RRRLRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRLRRLRL i else ntree10RRRLRRLRR (i - 8)

def ntree10RRRLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RRRLRRLL i else ntree10RRRLRRLR (i - 15)

def ntree10RRRLRRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨613,by decide⟩,⟨15,by decide⟩,⟨3716,by decide⟩] | 1 => ![⟨3392,by decide⟩,⟨308,by decide⟩,⟨3717,by decide⟩] | 2 => ![⟨3675,by decide⟩,⟨3617,by decide⟩,⟨3675,by decide⟩] | 3 => ![⟨3718,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩] | 4 => ![⟨3719,by decide⟩,⟨308,by decide⟩,⟨308,by decide⟩] | 5 => ![⟨3720,by decide⟩,⟨3182,by decide⟩,⟨3716,by decide⟩] | 6 => ![⟨3721,by decide⟩,⟨3166,by decide⟩,⟨3717,by decide⟩] | _ => ![⟨2355,by decide⟩,⟨2488,by decide⟩,⟨3722,by decide⟩]

def ntree10RRRLRRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3683,by decide⟩,⟨3684,by decide⟩,⟨3048,by decide⟩] | 1 => ![⟨3683,by decide⟩,⟨3683,by decide⟩,⟨2939,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨3723,by decide⟩] | 3 => ![⟨3724,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩] | 4 => ![⟨3725,by decide⟩,⟨3619,by decide⟩,⟨3512,by decide⟩] | 5 => ![⟨3726,by decide⟩,⟨595,by decide⟩,⟨595,by decide⟩] | 6 => ![⟨3620,by decide⟩,⟨3620,by decide⟩,⟨3723,by decide⟩] | _ => ![⟨3727,by decide⟩,⟨3621,by decide⟩,⟨3393,by decide⟩]

def ntree10RRRLRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRLRRRLL i else ntree10RRRLRRRLR (i - 8)

def ntree10RRRLRRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3682,by decide⟩,⟨3728,by decide⟩,⟨2367,by decide⟩] | 1 => ![⟨3576,by decide⟩,⟨3729,by decide⟩,⟨2488,by decide⟩] | 2 => ![⟨3730,by decide⟩,⟨3731,by decide⟩,⟨2308,by decide⟩] | 3 => ![⟨3730,by decide⟩,⟨3730,by decide⟩,⟨2307,by decide⟩] | 4 => ![⟨3732,by decide⟩,⟨3703,by decide⟩,⟨3733,by decide⟩] | 5 => ![⟨3734,by decide⟩,⟨1084,by decide⟩,⟨3733,by decide⟩] | 6 => ![⟨3735,by decide⟩,⟨2355,by decide⟩,⟨3735,by decide⟩] | _ => ![⟨3735,by decide⟩,⟨2409,by decide⟩,⟨3736,by decide⟩]

def ntree10RRRLRRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3358,by decide⟩,⟨1745,by decide⟩,⟨3360,by decide⟩] | 1 => ![⟨3663,by decide⟩,⟨2355,by decide⟩,⟨3663,by decide⟩] | 2 => ![⟨3663,by decide⟩,⟨2355,by decide⟩,⟨3665,by decide⟩] | 3 => ![⟨3737,by decide⟩,⟨15,by decide⟩,⟨3737,by decide⟩] | 4 => ![⟨3737,by decide⟩,⟨308,by decide⟩,⟨3738,by decide⟩] | 5 => ![⟨3735,by decide⟩,⟨3630,by decide⟩,⟨3735,by decide⟩] | 6 => ![⟨3739,by decide⟩,⟨3631,by decide⟩,⟨3736,by decide⟩] | _ => ![⟨3737,by decide⟩,⟨3632,by decide⟩,⟨3737,by decide⟩]

def ntree10RRRLRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRLRRRRL i else ntree10RRRLRRRRR (i - 8)

def ntree10RRRLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RRRLRRRL i else ntree10RRRLRRRR (i - 16)

def ntree10RRRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RRRLRRL i else ntree10RRRLRRR (i - 31)

def ntree10RRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10RRRLRL i else ntree10RRRLRR (i - 63)

def ntree10RRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 126 then ntree10RRRLL i else ntree10RRRLR (i - 126)

def ntree10RRRRLLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3740,by decide⟩,⟨3633,by decide⟩,⟨3738,by decide⟩] | 1 => ![⟨3730,by decide⟩,⟨3741,by decide⟩,⟨2543,by decide⟩] | 2 => ![⟨3656,by decide⟩,⟨3712,by decide⟩,⟨3722,by decide⟩] | 3 => ![⟨2355,by decide⟩,⟨2355,by decide⟩,⟨3644,by decide⟩] | 4 => ![⟨3371,by decide⟩,⟨2088,by decide⟩,⟨3371,by decide⟩] | 5 => ![⟨3358,by decide⟩,⟨595,by decide⟩,⟨3742,by decide⟩] | _ => ![⟨3743,by decide⟩,⟨979,by decide⟩,⟨3744,by decide⟩]

def ntree10RRRRLLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3745,by decide⟩,⟨3598,by decide⟩,⟨3735,by decide⟩] | 1 => ![⟨3746,by decide⟩,⟨3639,by decide⟩,⟨3359,by decide⟩] | 2 => ![⟨3747,by decide⟩,⟨3447,by decide⟩,⟨3742,by decide⟩] | 3 => ![⟨3748,by decide⟩,⟨3641,by decide⟩,⟨3744,by decide⟩] | 4 => ![⟨3562,by decide⟩,⟨3562,by decide⟩,⟨2307,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨3749,by decide⟩,⟨2939,by decide⟩] | 6 => ![⟨3750,by decide⟩,⟨3750,by decide⟩,⟨2939,by decide⟩] | _ => ![⟨3751,by decide⟩,⟨3752,by decide⟩,⟨3386,by decide⟩]

def ntree10RRRRLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RRRRLLLLL i else ntree10RRRRLLLLR (i - 7)

def ntree10RRRRLLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3753,by decide⟩,⟨3754,by decide⟩,⟨2936,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨2551,by decide⟩,⟨3755,by decide⟩] | 2 => ![⟨3756,by decide⟩,⟨3756,by decide⟩,⟨2939,by decide⟩] | 3 => ![⟨3757,by decide⟩,⟨3758,by decide⟩,⟨2941,by decide⟩] | 4 => ![⟨3759,by decide⟩,⟨15,by decide⟩,⟨2939,by decide⟩] | 5 => ![⟨3760,by decide⟩,⟨1637,by decide⟩,⟨2943,by decide⟩] | 6 => ![⟨2944,by decide⟩,⟨2197,by decide⟩,⟨3761,by decide⟩] | _ => ![⟨2954,by decide⟩,⟨2565,by decide⟩,⟨3762,by decide⟩]

def ntree10RRRRLLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨9,by decide⟩,⟨3763,by decide⟩,⟨9,by decide⟩] | 1 => ![⟨3764,by decide⟩,⟨3763,by decide⟩,⟨2937,by decide⟩] | 2 => ![⟨3765,by decide⟩,⟨3766,by decide⟩,⟨2939,by decide⟩] | 3 => ![⟨613,by decide⟩,⟨3767,by decide⟩,⟨613,by decide⟩] | 4 => ![⟨3768,by decide⟩,⟨3769,by decide⟩,⟨3410,by decide⟩] | 5 => ![⟨1184,by decide⟩,⟨9,by decide⟩,⟨3770,by decide⟩] | 6 => ![⟨1187,by decide⟩,⟨15,by decide⟩,⟨3771,by decide⟩] | _ => ![⟨1184,by decide⟩,⟨1656,by decide⟩,⟨3772,by decide⟩]

def ntree10RRRRLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRRLLLRL i else ntree10RRRRLLLRR (i - 8)

def ntree10RRRRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RRRRLLLL i else ntree10RRRRLLLR (i - 15)

def ntree10RRRRLLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1190,by decide⟩,⟨2572,by decide⟩,⟨3773,by decide⟩] | 1 => ![⟨3422,by decide⟩,⟨3766,by decide⟩,⟨3422,by decide⟩] | 2 => ![⟨3774,by decide⟩,⟨3775,by decide⟩,⟨3425,by decide⟩] | 3 => ![⟨3422,by decide⟩,⟨1663,by decide⟩,⟨3776,by decide⟩] | 4 => ![⟨3422,by decide⟩,⟨15,by decide⟩,⟨3425,by decide⟩] | 5 => ![⟨3428,by decide⟩,⟨1666,by decide⟩,⟨3777,by decide⟩] | 6 => ![⟨3778,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | _ => ![⟨3779,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩]

def ntree10RRRRLLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨3780,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨3781,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 2 => ![⟨1651,by decide⟩,⟨1651,by decide⟩,⟨3782,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨3766,by decide⟩,⟨2992,by decide⟩] | 4 => ![⟨3765,by decide⟩,⟨3783,by decide⟩,⟨2994,by decide⟩] | 5 => ![⟨613,by decide⟩,⟨2581,by decide⟩,⟨3784,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨2994,by decide⟩] | _ => ![⟨645,by decide⟩,⟨2583,by decide⟩,⟨3785,by decide⟩]

def ntree10RRRRLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRRLLRLL i else ntree10RRRRLLRLR (i - 8)

def ntree10RRRRLLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3786,by decide⟩,⟨3787,by decide⟩,⟨595,by decide⟩] | 1 => ![⟨3788,by decide⟩,⟨3787,by decide⟩,⟨3393,by decide⟩] | 2 => ![⟨3786,by decide⟩,⟨3789,by decide⟩,⟨1663,by decide⟩] | 3 => ![⟨3790,by decide⟩,⟨3789,by decide⟩,⟨2965,by decide⟩] | 4 => ![⟨2585,by decide⟩,⟨2585,by decide⟩,⟨3791,by decide⟩] | 5 => ![⟨3792,by decide⟩,⟨2586,by decide⟩,⟨3793,by decide⟩] | 6 => ![⟨3794,by decide⟩,⟨2586,by decide⟩,⟨3795,by decide⟩] | _ => ![⟨3794,by decide⟩,⟨2593,by decide⟩,⟨3796,by decide⟩]

def ntree10RRRRLLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3797,by decide⟩,⟨595,by decide⟩,⟨595,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨3780,by decide⟩,⟨14,by decide⟩] | 2 => ![⟨3798,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨3008,by decide⟩,⟨2599,by decide⟩,⟨3799,by decide⟩] | 4 => ![⟨97,by decide⟩,⟨3800,by decide⟩,⟨1715,by decide⟩] | 5 => ![⟨1238,by decide⟩,⟨3800,by decide⟩,⟨3457,by decide⟩] | 6 => ![⟨3801,by decide⟩,⟨97,by decide⟩,⟨3392,by decide⟩] | _ => ![⟨3802,by decide⟩,⟨3459,by decide⟩,⟨18,by decide⟩]

def ntree10RRRRLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRRLLRRL i else ntree10RRRRLLRRR (i - 8)

def ntree10RRRRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RRRRLLRL i else ntree10RRRRLLRR (i - 16)

def ntree10RRRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RRRRLLL i else ntree10RRRRLLR (i - 31)

def ntree10RRRRLRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3803,by decide⟩,⟨3017,by decide⟩,⟨3396,by decide⟩] | 1 => ![⟨95,by decide⟩,⟨3804,by decide⟩,⟨1747,by decide⟩] | 2 => ![⟨97,by decide⟩,⟨3805,by decide⟩,⟨1749,by decide⟩] | 3 => ![⟨1253,by decide⟩,⟨3806,by decide⟩,⟨3472,by decide⟩] | 4 => ![⟨1184,by decide⟩,⟨1747,by decide⟩,⟨3807,by decide⟩] | 5 => ![⟨1187,by decide⟩,⟨1749,by decide⟩,⟨3808,by decide⟩] | _ => ![⟨15,by decide⟩,⟨2641,by decide⟩,⟨2641,by decide⟩]

def ntree10RRRRLRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3809,by decide⟩,⟨3805,by decide⟩,⟨3810,by decide⟩] | 1 => ![⟨3809,by decide⟩,⟨97,by decide⟩,⟨3422,by decide⟩] | 2 => ![⟨3476,by decide⟩,⟨3459,by decide⟩,⟨3422,by decide⟩] | 3 => ![⟨3811,by decide⟩,⟨3017,by decide⟩,⟨3428,by decide⟩] | 4 => ![⟨3428,by decide⟩,⟨1752,by decide⟩,⟨3812,by decide⟩] | 5 => ![⟨97,by decide⟩,⟨3813,by decide⟩,⟨2685,by decide⟩] | 6 => ![⟨1637,by decide⟩,⟨2654,by decide⟩,⟨2654,by decide⟩] | _ => ![⟨15,by decide⟩,⟨3814,by decide⟩,⟨1715,by decide⟩]

def ntree10RRRRLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RRRRLRLLL i else ntree10RRRRLRLLR (i - 7)

def ntree10RRRRLRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨97,by decide⟩,⟨3815,by decide⟩,⟨1768,by decide⟩] | 1 => ![⟨613,by decide⟩,⟨1715,by decide⟩,⟨3490,by decide⟩] | 2 => ![⟨613,by decide⟩,⟨1749,by decide⟩,⟨3816,by decide⟩] | 3 => ![⟨2613,by decide⟩,⟨3766,by decide⟩,⟨3817,by decide⟩] | 4 => ![⟨3801,by decide⟩,⟨3805,by decide⟩,⟨3818,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨3819,by decide⟩] | 6 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨3819,by decide⟩] | _ => ![⟨3820,by decide⟩,⟨3820,by decide⟩,⟨2585,by decide⟩]

def ntree10RRRRLRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3821,by decide⟩,⟨3820,by decide⟩,⟨3792,by decide⟩] | 1 => ![⟨3822,by decide⟩,⟨15,by decide⟩,⟨613,by decide⟩] | 2 => ![⟨613,by decide⟩,⟨109,by decide⟩,⟨3823,by decide⟩] | 3 => ![⟨3392,by decide⟩,⟨1749,by decide⟩,⟨3818,by decide⟩] | 4 => ![⟨2997,by decide⟩,⟨2266,by decide⟩,⟨3824,by decide⟩] | 5 => ![⟨3794,by decide⟩,⟨2585,by decide⟩,⟨3794,by decide⟩] | 6 => ![⟨3792,by decide⟩,⟨2585,by decide⟩,⟨3792,by decide⟩] | _ => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨3825,by decide⟩]

def ntree10RRRRLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRRLRLRL i else ntree10RRRRLRLRR (i - 8)

def ntree10RRRRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RRRRLRLL i else ntree10RRRRLRLR (i - 15)

def ntree10RRRRLRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨3825,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨2685,by decide⟩,⟨3826,by decide⟩] | 2 => ![⟨96,by decide⟩,⟨3813,by decide⟩,⟨3826,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨3497,by decide⟩] | 4 => ![⟨1695,by decide⟩,⟨1695,by decide⟩,⟨3827,by decide⟩] | 5 => ![⟨3008,by decide⟩,⟨2684,by decide⟩,⟨3828,by decide⟩] | 6 => ![⟨3829,by decide⟩,⟨3829,by decide⟩,⟨3502,by decide⟩] | _ => ![⟨3830,by decide⟩,⟨3831,by decide⟩,⟨3499,by decide⟩]

def ntree10RRRRLRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2613,by decide⟩,⟨1309,by decide⟩,⟨2939,by decide⟩] | 1 => ![⟨3801,by decide⟩,⟨1296,by decide⟩,⟨3393,by decide⟩] | 2 => ![⟨3802,by decide⟩,⟨3832,by decide⟩,⟨2941,by decide⟩] | 3 => ![⟨3833,by decide⟩,⟨15,by decide⟩,⟨2939,by decide⟩] | 4 => ![⟨3834,by decide⟩,⟨97,by decide⟩,⟨3512,by decide⟩] | 5 => ![⟨1319,by decide⟩,⟨3072,by decide⟩,⟨3524,by decide⟩] | 6 => ![⟨3835,by decide⟩,⟨3836,by decide⟩,⟨3525,by decide⟩] | _ => ![⟨1315,by decide⟩,⟨1656,by decide⟩,⟨3837,by decide⟩]

def ntree10RRRRLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRRLRRLL i else ntree10RRRRLRRLR (i - 8)

def ntree10RRRRLRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨1315,by decide⟩,⟨2639,by decide⟩,⟨3838,by decide⟩] | 1 => ![⟨1318,by decide⟩,⟨2704,by decide⟩,⟨3839,by decide⟩] | 2 => ![⟨3809,by decide⟩,⟨3066,by decide⟩,⟨3776,by decide⟩] | 3 => ![⟨3476,by decide⟩,⟨3840,by decide⟩,⟨3425,by decide⟩] | 4 => ![⟨3422,by decide⟩,⟨166,by decide⟩,⟨3841,by decide⟩] | 5 => ![⟨3842,by decide⟩,⟨166,by decide⟩,⟨3080,by decide⟩] | 6 => ![⟨772,by decide⟩,⟨1663,by decide⟩,⟨3843,by decide⟩] | _ => ![⟨3844,by decide⟩,⟨15,by decide⟩,⟨3845,by decide⟩]

def ntree10RRRRLRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨794,by decide⟩,⟨794,by decide⟩,⟨3555,by decide⟩] | 1 => ![⟨794,by decide⟩,⟨794,by decide⟩,⟨3846,by decide⟩] | 2 => ![⟨797,by decide⟩,⟨2714,by decide⟩,⟨3847,by decide⟩] | 3 => ![⟨3820,by decide⟩,⟨3848,by decide⟩,⟨2586,by decide⟩] | 4 => ![⟨2667,by decide⟩,⟨3849,by decide⟩,⟨3791,by decide⟩] | 5 => ![⟨3821,by decide⟩,⟨3848,by decide⟩,⟨3793,by decide⟩] | 6 => ![⟨3850,by decide⟩,⟨1309,by decide⟩,⟨3497,by decide⟩] | _ => ![⟨2355,by decide⟩,⟨2355,by decide⟩,⟨3851,by decide⟩]

def ntree10RRRRLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRRLRRRL i else ntree10RRRRLRRRR (i - 8)

def ntree10RRRRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RRRRLRRL i else ntree10RRRRLRRR (i - 16)

def ntree10RRRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RRRRLRL i else ntree10RRRRLRR (i - 31)

def ntree10RRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10RRRRLL i else ntree10RRRRLR (i - 63)

def ntree10RRRRRLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3570,by decide⟩,⟨2727,by decide⟩,⟨3852,by decide⟩] | 1 => ![⟨3103,by decide⟩,⟨2186,by decide⟩,⟨3853,by decide⟩] | 2 => ![⟨3854,by decide⟩,⟨3854,by decide⟩,⟨2355,by decide⟩] | 3 => ![⟨3854,by decide⟩,⟨3855,by decide⟩,⟨2727,by decide⟩] | 4 => ![⟨2355,by decide⟩,⟨3856,by decide⟩,⟨2355,by decide⟩] | 5 => ![⟨3857,by decide⟩,⟨3856,by decide⟩,⟨3851,by decide⟩] | _ => ![⟨3858,by decide⟩,⟨3766,by decide⟩,⟨1329,by decide⟩]

def ntree10RRRRRLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨1663,by decide⟩,⟨3859,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨3860,by decide⟩,⟨1663,by decide⟩] | 2 => ![⟨3861,by decide⟩,⟨836,by decide⟩,⟨3101,by decide⟩] | 3 => ![⟨3862,by decide⟩,⟨1663,by decide⟩,⟨1663,by decide⟩] | 4 => ![⟨3863,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩] | 5 => ![⟨3864,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨3865,by decide⟩,⟨225,by decide⟩,⟨3583,by decide⟩] | _ => ![⟨3866,by decide⟩,⟨2355,by decide⟩,⟨3866,by decide⟩]

def ntree10RRRRRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10RRRRRLLLL i else ntree10RRRRRLLLR (i - 7)

def ntree10RRRRRLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3866,by decide⟩,⟨2355,by decide⟩,⟨3867,by decide⟩] | 1 => ![⟨1187,by decide⟩,⟨1663,by decide⟩,⟨3868,by decide⟩] | 2 => ![⟨1187,by decide⟩,⟨15,by decide⟩,⟨3869,by decide⟩] | 3 => ![⟨3854,by decide⟩,⟨3870,by decide⟩,⟨2355,by decide⟩] | 4 => ![⟨193,by decide⟩,⟨3871,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨193,by decide⟩,⟨3872,by decide⟩,⟨1663,by decide⟩] | 6 => ![⟨3873,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩] | _ => ![⟨3874,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩]

def ntree10RRRRRLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨3875,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨3876,by decide⟩,⟨3875,by decide⟩,⟨637,by decide⟩] | 2 => ![⟨3877,by decide⟩,⟨2365,by decide⟩,⟨2365,by decide⟩] | 3 => ![⟨3878,by decide⟩,⟨1637,by decide⟩,⟨1637,by decide⟩] | 4 => ![⟨3879,by decide⟩,⟨3129,by decide⟩,⟨3438,by decide⟩] | 5 => ![⟨2355,by decide⟩,⟨3856,by decide⟩,⟨3880,by decide⟩] | 6 => ![⟨3570,by decide⟩,⟨2745,by decide⟩,⟨3881,by decide⟩] | _ => ![⟨14,by decide⟩,⟨3860,by decide⟩,⟨2987,by decide⟩]

def ntree10RRRRRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRRRLLRL i else ntree10RRRRRLLRR (i - 8)

def ntree10RRRRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10RRRRRLLL i else ntree10RRRRRLLR (i - 15)

def ntree10RRRRRLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2355,by decide⟩,⟨2355,by decide⟩,⟨3880,by decide⟩] | 1 => ![⟨3103,by decide⟩,⟨15,by decide⟩,⟨3139,by decide⟩] | 2 => ![⟨3882,by decide⟩,⟨3883,by decide⟩,⟨2367,by decide⟩] | 3 => ![⟨3882,by decide⟩,⟨3884,by decide⟩,⟨2745,by decide⟩] | 4 => ![⟨3885,by decide⟩,⟨3886,by decide⟩,⟨2586,by decide⟩] | 5 => ![⟨2585,by decide⟩,⟨3887,by decide⟩,⟨2585,by decide⟩] | 6 => ![⟨3888,by decide⟩,⟨1391,by decide⟩,⟨15,by decide⟩] | _ => ![⟨3889,by decide⟩,⟨2355,by decide⟩,⟨2355,by decide⟩]

def ntree10RRRRRLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3890,by decide⟩,⟨1391,by decide⟩,⟨14,by decide⟩] | 1 => ![⟨3891,by decide⟩,⟨3891,by decide⟩,⟨2355,by decide⟩] | 2 => ![⟨3892,by decide⟩,⟨3891,by decide⟩,⟨3570,by decide⟩] | 3 => ![⟨3103,by decide⟩,⟨1401,by decide⟩,⟨3893,by decide⟩] | 4 => ![⟨3459,by decide⟩,⟨3894,by decide⟩,⟨1401,by decide⟩] | 5 => ![⟨3895,by decide⟩,⟨3895,by decide⟩,⟨2365,by decide⟩] | 6 => ![⟨3896,by decide⟩,⟨3895,by decide⟩,⟨3578,by decide⟩] | _ => ![⟨3891,by decide⟩,⟨3897,by decide⟩,⟨2794,by decide⟩]

def ntree10RRRRRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRRRLRLL i else ntree10RRRRRLRLR (i - 8)

def ntree10RRRRRLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3866,by decide⟩,⟨2794,by decide⟩,⟨3898,by decide⟩] | 1 => ![⟨3459,by decide⟩,⟨3899,by decide⟩,⟨1948,by decide⟩] | 2 => ![⟨3103,by decide⟩,⟨1749,by decide⟩,⟨3180,by decide⟩] | 3 => ![⟨3820,by decide⟩,⟨3900,by decide⟩,⟨2808,by decide⟩] | 4 => ![⟨1988,by decide⟩,⟨1988,by decide⟩,⟨3901,by decide⟩] | 5 => ![⟨3193,by decide⟩,⟨2823,by decide⟩,⟨3902,by decide⟩] | 6 => ![⟨3891,by decide⟩,⟨3903,by decide⟩,⟨2367,by decide⟩] | _ => ![⟨2355,by decide⟩,⟨3904,by decide⟩,⟨2355,by decide⟩]

def ntree10RRRRRLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3459,by decide⟩,⟨3832,by decide⟩,⟨1634,by decide⟩] | 1 => ![⟨3891,by decide⟩,⟨3905,by decide⟩,⟨2745,by decide⟩] | 2 => ![⟨2355,by decide⟩,⟨3626,by decide⟩,⟨3851,by decide⟩] | 3 => ![⟨97,by decide⟩,⟨3066,by decide⟩,⟨3859,by decide⟩] | 4 => ![⟨3906,by decide⟩,⟨2745,by decide⟩,⟨3907,by decide⟩] | 5 => ![⟨3906,by decide⟩,⟨2409,by decide⟩,⟨3908,by decide⟩] | 6 => ![⟨3909,by decide⟩,⟨2018,by decide⟩,⟨3910,by decide⟩] | _ => ![⟨3459,by decide⟩,⟨3840,by decide⟩,⟨15,by decide⟩]

def ntree10RRRRRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRRRLRRL i else ntree10RRRRRLRRR (i - 8)

def ntree10RRRRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RRRRRLRL i else ntree10RRRRRLRR (i - 16)

def ntree10RRRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10RRRRRLL i else ntree10RRRRRLR (i - 31)

def ntree10RRRRRRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3911,by decide⟩,⟨97,by decide⟩,⟨958,by decide⟩] | 1 => ![⟨3891,by decide⟩,⟨3891,by decide⟩,⟨3880,by decide⟩] | 2 => ![⟨3892,by decide⟩,⟨3905,by decide⟩,⟨3881,by decide⟩] | 3 => ![⟨1988,by decide⟩,⟨1988,by decide⟩,⟨3222,by decide⟩] | 4 => ![⟨2585,by decide⟩,⟨3849,by decide⟩,⟨2585,by decide⟩] | 5 => ![⟨3912,by decide⟩,⟨3904,by decide⟩,⟨3613,by decide⟩] | 6 => ![⟨2853,by decide⟩,⟨2853,by decide⟩,⟨3913,by decide⟩] | _ => ![⟨2856,by decide⟩,⟨2856,by decide⟩,⟨3914,by decide⟩]

def ntree10RRRRRRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3915,by decide⟩,⟨2355,by decide⟩,⟨3644,by decide⟩] | 1 => ![⟨3916,by decide⟩,⟨2860,by decide⟩,⟨3917,by decide⟩] | 2 => ![⟨3918,by decide⟩,⟨2355,by decide⟩,⟨3644,by decide⟩] | 3 => ![⟨3919,by decide⟩,⟨2365,by decide⟩,⟨3652,by decide⟩] | 4 => ![⟨3920,by decide⟩,⟨15,by decide⟩,⟨613,by decide⟩] | 5 => ![⟨3921,by decide⟩,⟨2853,by decide⟩,⟨3921,by decide⟩] | 6 => ![⟨3921,by decide⟩,⟨2853,by decide⟩,⟨3922,by decide⟩] | _ => ![⟨3923,by decide⟩,⟨2856,by decide⟩,⟨3924,by decide⟩]

def ntree10RRRRRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRRRRLLL i else ntree10RRRRRRLLR (i - 8)

def ntree10RRRRRRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨454,by decide⟩,⟨3875,by decide⟩,⟨2939,by decide⟩] | 1 => ![⟨3925,by decide⟩,⟨15,by decide⟩,⟨3422,by decide⟩] | 2 => ![⟨3926,by decide⟩,⟨1637,by decide⟩,⟨3428,by decide⟩] | 3 => ![⟨2856,by decide⟩,⟨3927,by decide⟩,⟨2856,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨2992,by decide⟩] | 5 => ![⟨3928,by decide⟩,⟨3929,by decide⟩,⟨2939,by decide⟩] | 6 => ![⟨3659,by decide⟩,⟨2875,by decide⟩,⟨3930,by decide⟩] | _ => ![⟨3329,by decide⟩,⟨2064,by decide⟩,⟨3290,by decide⟩]

def ntree10RRRRRRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨2871,by decide⟩,⟨2355,by decide⟩,⟨3677,by decide⟩] | 1 => ![⟨3931,by decide⟩,⟨225,by decide⟩,⟨3678,by decide⟩] | 2 => ![⟨3920,by decide⟩,⟨595,by decide⟩,⟨657,by decide⟩] | 3 => ![⟨3932,by decide⟩,⟨1391,by decide⟩,⟨3410,by decide⟩] | 4 => ![⟨3933,by decide⟩,⟨1393,by decide⟩,⟨3393,by decide⟩] | 5 => ![⟨3934,by decide⟩,⟨3935,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨3936,by decide⟩,⟨3936,by decide⟩,⟨2853,by decide⟩] | _ => ![⟨3937,by decide⟩,⟨3937,by decide⟩,⟨2856,by decide⟩]

def ntree10RRRRRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRRRRLRL i else ntree10RRRRRRLRR (i - 8)

def ntree10RRRRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RRRRRRLL i else ntree10RRRRRRLR (i - 16)

def ntree10RRRRRRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3916,by decide⟩,⟨2856,by decide⟩,⟨3916,by decide⟩] | 1 => ![⟨2613,by decide⟩,⟨15,by decide⟩,⟨1062,by decide⟩] | 2 => ![⟨2618,by decide⟩,⟨1637,by decide⟩,⟨3696,by decide⟩] | 3 => ![⟨3938,by decide⟩,⟨3891,by decide⟩,⟨3659,by decide⟩] | 4 => ![⟨3923,by decide⟩,⟨2856,by decide⟩,⟨3923,by decide⟩] | 5 => ![⟨3939,by decide⟩,⟨3891,by decide⟩,⟨3663,by decide⟩] | 6 => ![⟨3422,by decide⟩,⟨1948,by decide⟩,⟨3708,by decide⟩] | _ => ![⟨3940,by decide⟩,⟨3895,by decide⟩,⟨3666,by decide⟩]

def ntree10RRRRRRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3937,by decide⟩,⟨3941,by decide⟩,⟨2899,by decide⟩] | 1 => ![⟨3329,by decide⟩,⟨15,by decide⟩,⟨3329,by decide⟩] | 2 => ![⟨3942,by decide⟩,⟨2355,by decide⟩,⟨3659,by decide⟩] | 3 => ![⟨3943,by decide⟩,⟨97,by decide⟩,⟨3675,by decide⟩] | 4 => ![⟨1253,by decide⟩,⟨97,by decide⟩,⟨3716,by decide⟩] | 5 => ![⟨3822,by decide⟩,⟨308,by decide⟩,⟨1089,by decide⟩] | 6 => ![⟨3801,by decide⟩,⟨309,by decide⟩,⟨3717,by decide⟩] | _ => ![⟨2355,by decide⟩,⟨2910,by decide⟩,⟨2910,by decide⟩]

def ntree10RRRRRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRRRRRLL i else ntree10RRRRRRRLR (i - 8)

def ntree10RRRRRRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3937,by decide⟩,⟨3937,by decide⟩,⟨3914,by decide⟩] | 1 => ![⟨3944,by decide⟩,⟨2856,by decide⟩,⟨3945,by decide⟩] | 2 => ![⟨2887,by decide⟩,⟨3904,by decide⟩,⟨3644,by decide⟩] | 3 => ![⟨3946,by decide⟩,⟨1309,by decide⟩,⟨3723,by decide⟩] | 4 => ![⟨3936,by decide⟩,⟨3947,by decide⟩,⟨2863,by decide⟩] | 5 => ![⟨2853,by decide⟩,⟨3948,by decide⟩,⟨2853,by decide⟩] | 6 => ![⟨3937,by decide⟩,⟨3949,by decide⟩,⟨2864,by decide⟩] | _ => ![⟨3950,by decide⟩,⟨3891,by decide⟩,⟨3735,by decide⟩]

def ntree10RRRRRRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3951,by decide⟩,⟨2853,by decide⟩,⟨3951,by decide⟩] | 1 => ![⟨3951,by decide⟩,⟨2894,by decide⟩,⟨3952,by decide⟩] | 2 => ![⟨3953,by decide⟩,⟨2895,by decide⟩,⟨3954,by decide⟩] | 3 => ![⟨3955,by decide⟩,⟨97,by decide⟩,⟨3737,by decide⟩] | 4 => ![⟨3735,by decide⟩,⟨2355,by decide⟩,⟨3956,by decide⟩] | 5 => ![⟨3357,by decide⟩,⟨1296,by decide⟩,⟨3742,by decide⟩] | 6 => ![⟨3957,by decide⟩,⟨1480,by decide⟩,⟨3359,by decide⟩] | _ => ![⟨3958,by decide⟩,⟨1482,by decide⟩,⟨3744,by decide⟩]

def ntree10RRRRRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10RRRRRRRRL i else ntree10RRRRRRRRR (i - 8)

def ntree10RRRRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10RRRRRRRL i else ntree10RRRRRRRR (i - 16)

def ntree10RRRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 32 then ntree10RRRRRRL i else ntree10RRRRRRR (i - 32)

def ntree10RRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10RRRRRL i else ntree10RRRRRR (i - 63)

def ntree10RRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 126 then ntree10RRRRL i else ntree10RRRRR (i - 126)

def ntree10RRR (i : Nat) : Fin 3 → Fin 3959 := if i < 252 then ntree10RRRL i else ntree10RRRR (i - 252)

def ntree10RR (i : Nat) : Fin 3 → Fin 3959 := if i < 504 then ntree10RRL i else ntree10RRR (i - 504)

def ntree10R (i : Nat) : Fin 3 → Fin 3959 := if i < 1008 then ntree10RL i else ntree10RR (i - 1008)

def ntree10 (i : Nat) : Fin 3 → Fin 3959 := if i < 2016 then ntree10L i else ntree10R (i - 2016)

def layer10 : Fin 3959 → State := fun i => stree10 i.val

def next10 : Fin 4033 → Fin 3 → Fin 3959 := fun i => ntree10 i.val

end Paper2.Certificates.Q6.Coverage
