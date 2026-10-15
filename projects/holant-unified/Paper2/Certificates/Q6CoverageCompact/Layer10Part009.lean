import Paper2.Certificates.Q6CoverageCompact.Layer10Part008

namespace Paper2.Certificates.Q6.Coverage

def stree10RLRLLLRRR (i : Nat) : State := match i with | 0 => state10_2527 | 1 => state10_2528 | 2 => state10_2529 | 3 => state10_2530 | 4 => state10_2531 | 5 => state10_2532 | 6 => state10_2533 | _ => state10_2534

def stree10RLRLLLRR (i : Nat) : State := if i < 8 then stree10RLRLLLRRL i else stree10RLRLLLRRR (i - 8)

def stree10RLRLLLR (i : Nat) : State := if i < 15 then stree10RLRLLLRL i else stree10RLRLLLRR (i - 15)

def stree10RLRLLL (i : Nat) : State := if i < 30 then stree10RLRLLLL i else stree10RLRLLLR (i - 30)

def stree10RLRLLRLLL (i : Nat) : State := match i with | 0 => state10_2535 | 1 => state10_2536 | 2 => state10_2537 | 3 => state10_2538 | 4 => state10_2539 | 5 => state10_2540 | _ => state10_2541

def stree10RLRLLRLLR (i : Nat) : State := match i with | 0 => state10_2542 | 1 => state10_2543 | 2 => state10_2544 | 3 => state10_2545 | 4 => state10_2546 | 5 => state10_2547 | 6 => state10_2548 | _ => state10_2549

def stree10RLRLLRLL (i : Nat) : State := if i < 7 then stree10RLRLLRLLL i else stree10RLRLLRLLR (i - 7)

def stree10RLRLLRLRL (i : Nat) : State := match i with | 0 => state10_2550 | 1 => state10_2551 | 2 => state10_2552 | 3 => state10_2553 | 4 => state10_2554 | 5 => state10_2555 | 6 => state10_2556 | _ => state10_2557

def stree10RLRLLRLRR (i : Nat) : State := match i with | 0 => state10_2558 | 1 => state10_2559 | 2 => state10_2560 | 3 => state10_2561 | 4 => state10_2562 | 5 => state10_2563 | 6 => state10_2564 | _ => state10_2565

def stree10RLRLLRLR (i : Nat) : State := if i < 8 then stree10RLRLLRLRL i else stree10RLRLLRLRR (i - 8)

def stree10RLRLLRL (i : Nat) : State := if i < 15 then stree10RLRLLRLL i else stree10RLRLLRLR (i - 15)

def stree10RLRLLRRLL (i : Nat) : State := match i with | 0 => state10_2566 | 1 => state10_2567 | 2 => state10_2568 | 3 => state10_2569 | 4 => state10_2570 | 5 => state10_2571 | _ => state10_2572

def stree10RLRLLRRLR (i : Nat) : State := match i with | 0 => state10_2573 | 1 => state10_2574 | 2 => state10_2575 | 3 => state10_2576 | 4 => state10_2577 | 5 => state10_2578 | 6 => state10_2579 | _ => state10_2580

def stree10RLRLLRRL (i : Nat) : State := if i < 7 then stree10RLRLLRRLL i else stree10RLRLLRRLR (i - 7)

def stree10RLRLLRRRL (i : Nat) : State := match i with | 0 => state10_2581 | 1 => state10_2582 | 2 => state10_2583 | 3 => state10_2584 | 4 => state10_2585 | 5 => state10_2586 | 6 => state10_2587 | _ => state10_2588

def stree10RLRLLRRRR (i : Nat) : State := match i with | 0 => state10_2589 | 1 => state10_2590 | 2 => state10_2591 | 3 => state10_2592 | 4 => state10_2593 | 5 => state10_2594 | 6 => state10_2595 | _ => state10_2596

def stree10RLRLLRRR (i : Nat) : State := if i < 8 then stree10RLRLLRRRL i else stree10RLRLLRRRR (i - 8)

def stree10RLRLLRR (i : Nat) : State := if i < 15 then stree10RLRLLRRL i else stree10RLRLLRRR (i - 15)

def stree10RLRLLR (i : Nat) : State := if i < 31 then stree10RLRLLRL i else stree10RLRLLRR (i - 31)

def stree10RLRLL (i : Nat) : State := if i < 61 then stree10RLRLLL i else stree10RLRLLR (i - 61)

def stree10RLRLRLLLL (i : Nat) : State := match i with | 0 => state10_2597 | 1 => state10_2598 | 2 => state10_2599 | 3 => state10_2600 | 4 => state10_2601 | 5 => state10_2602 | _ => state10_2603

def stree10RLRLRLLLR (i : Nat) : State := match i with | 0 => state10_2604 | 1 => state10_2605 | 2 => state10_2606 | 3 => state10_2607 | 4 => state10_2608 | 5 => state10_2609 | 6 => state10_2610 | _ => state10_2611

def stree10RLRLRLLL (i : Nat) : State := if i < 7 then stree10RLRLRLLLL i else stree10RLRLRLLLR (i - 7)

def stree10RLRLRLLRL (i : Nat) : State := match i with | 0 => state10_2612 | 1 => state10_2613 | 2 => state10_2614 | 3 => state10_2615 | 4 => state10_2616 | 5 => state10_2617 | 6 => state10_2618 | _ => state10_2619

def stree10RLRLRLLRR (i : Nat) : State := match i with | 0 => state10_2620 | 1 => state10_2621 | 2 => state10_2622 | 3 => state10_2623 | 4 => state10_2624 | 5 => state10_2625 | 6 => state10_2626 | _ => state10_2627

def stree10RLRLRLLR (i : Nat) : State := if i < 8 then stree10RLRLRLLRL i else stree10RLRLRLLRR (i - 8)

def stree10RLRLRLL (i : Nat) : State := if i < 15 then stree10RLRLRLLL i else stree10RLRLRLLR (i - 15)

def stree10RLRLRLRLL (i : Nat) : State := match i with | 0 => state10_2628 | 1 => state10_2629 | 2 => state10_2630 | 3 => state10_2631 | 4 => state10_2632 | 5 => state10_2633 | _ => state10_2634

def stree10RLRLRLRLR (i : Nat) : State := match i with | 0 => state10_2635 | 1 => state10_2636 | 2 => state10_2637 | 3 => state10_2638 | 4 => state10_2639 | 5 => state10_2640 | 6 => state10_2641 | _ => state10_2642

def stree10RLRLRLRL (i : Nat) : State := if i < 7 then stree10RLRLRLRLL i else stree10RLRLRLRLR (i - 7)

def stree10RLRLRLRRL (i : Nat) : State := match i with | 0 => state10_2643 | 1 => state10_2644 | 2 => state10_2645 | 3 => state10_2646 | 4 => state10_2647 | 5 => state10_2648 | 6 => state10_2649 | _ => state10_2650

def stree10RLRLRLRRR (i : Nat) : State := match i with | 0 => state10_2651 | 1 => state10_2652 | 2 => state10_2653 | 3 => state10_2654 | 4 => state10_2655 | 5 => state10_2656 | 6 => state10_2657 | _ => state10_2658

def stree10RLRLRLRR (i : Nat) : State := if i < 8 then stree10RLRLRLRRL i else stree10RLRLRLRRR (i - 8)

def stree10RLRLRLR (i : Nat) : State := if i < 15 then stree10RLRLRLRL i else stree10RLRLRLRR (i - 15)

def stree10RLRLRL (i : Nat) : State := if i < 31 then stree10RLRLRLL i else stree10RLRLRLR (i - 31)

def stree10RLRLRRLLL (i : Nat) : State := match i with | 0 => state10_2659 | 1 => state10_2660 | 2 => state10_2661 | 3 => state10_2662 | 4 => state10_2663 | 5 => state10_2664 | _ => state10_2665

def stree10RLRLRRLLR (i : Nat) : State := match i with | 0 => state10_2666 | 1 => state10_2667 | 2 => state10_2668 | 3 => state10_2669 | 4 => state10_2670 | 5 => state10_2671 | 6 => state10_2672 | _ => state10_2673

def stree10RLRLRRLL (i : Nat) : State := if i < 7 then stree10RLRLRRLLL i else stree10RLRLRRLLR (i - 7)

def stree10RLRLRRLRL (i : Nat) : State := match i with | 0 => state10_2674 | 1 => state10_2675 | 2 => state10_2676 | 3 => state10_2677 | 4 => state10_2678 | 5 => state10_2679 | 6 => state10_2680 | _ => state10_2681

def stree10RLRLRRLRR (i : Nat) : State := match i with | 0 => state10_2682 | 1 => state10_2683 | 2 => state10_2684 | 3 => state10_2685 | 4 => state10_2686 | 5 => state10_2687 | 6 => state10_2688 | _ => state10_2689

def stree10RLRLRRLR (i : Nat) : State := if i < 8 then stree10RLRLRRLRL i else stree10RLRLRRLRR (i - 8)

def stree10RLRLRRL (i : Nat) : State := if i < 15 then stree10RLRLRRLL i else stree10RLRLRRLR (i - 15)

def stree10RLRLRRRLL (i : Nat) : State := match i with | 0 => state10_2690 | 1 => state10_2691 | 2 => state10_2692 | 3 => state10_2693 | 4 => state10_2694 | 5 => state10_2695 | _ => state10_2696

def stree10RLRLRRRLR (i : Nat) : State := match i with | 0 => state10_2697 | 1 => state10_2698 | 2 => state10_2699 | 3 => state10_2700 | 4 => state10_2701 | 5 => state10_2702 | 6 => state10_2703 | _ => state10_2704

def stree10RLRLRRRL (i : Nat) : State := if i < 7 then stree10RLRLRRRLL i else stree10RLRLRRRLR (i - 7)

def stree10RLRLRRRRL (i : Nat) : State := match i with | 0 => state10_2705 | 1 => state10_2706 | 2 => state10_2707 | 3 => state10_2708 | 4 => state10_2709 | 5 => state10_2710 | 6 => state10_2711 | _ => state10_2712

def stree10RLRLRRRRR (i : Nat) : State := match i with | 0 => state10_2713 | 1 => state10_2714 | 2 => state10_2715 | 3 => state10_2716 | 4 => state10_2717 | 5 => state10_2718 | 6 => state10_2719 | _ => state10_2720

def stree10RLRLRRRR (i : Nat) : State := if i < 8 then stree10RLRLRRRRL i else stree10RLRLRRRRR (i - 8)

def stree10RLRLRRR (i : Nat) : State := if i < 15 then stree10RLRLRRRL i else stree10RLRLRRRR (i - 15)

def stree10RLRLRR (i : Nat) : State := if i < 31 then stree10RLRLRRL i else stree10RLRLRRR (i - 31)

def stree10RLRLR (i : Nat) : State := if i < 62 then stree10RLRLRL i else stree10RLRLRR (i - 62)

def stree10RLRL (i : Nat) : State := if i < 123 then stree10RLRLL i else stree10RLRLR (i - 123)

def stree10RLRRLLLLL (i : Nat) : State := match i with | 0 => state10_2721 | 1 => state10_2722 | 2 => state10_2723 | 3 => state10_2724 | 4 => state10_2725 | 5 => state10_2726 | _ => state10_2727

def stree10RLRRLLLLR (i : Nat) : State := match i with | 0 => state10_2728 | 1 => state10_2729 | 2 => state10_2730 | 3 => state10_2731 | 4 => state10_2732 | 5 => state10_2733 | 6 => state10_2734 | _ => state10_2735

def stree10RLRRLLLL (i : Nat) : State := if i < 7 then stree10RLRRLLLLL i else stree10RLRRLLLLR (i - 7)

def stree10RLRRLLLRL (i : Nat) : State := match i with | 0 => state10_2736 | 1 => state10_2737 | 2 => state10_2738 | 3 => state10_2739 | 4 => state10_2740 | 5 => state10_2741 | 6 => state10_2742 | _ => state10_2743

def stree10RLRRLLLRR (i : Nat) : State := match i with | 0 => state10_2744 | 1 => state10_2745 | 2 => state10_2746 | 3 => state10_2747 | 4 => state10_2748 | 5 => state10_2749 | 6 => state10_2750 | _ => state10_2751

def stree10RLRRLLLR (i : Nat) : State := if i < 8 then stree10RLRRLLLRL i else stree10RLRRLLLRR (i - 8)

def stree10RLRRLLL (i : Nat) : State := if i < 15 then stree10RLRRLLLL i else stree10RLRRLLLR (i - 15)

def stree10RLRRLLRLL (i : Nat) : State := match i with | 0 => state10_2752 | 1 => state10_2753 | 2 => state10_2754 | 3 => state10_2755 | 4 => state10_2756 | 5 => state10_2757 | _ => state10_2758

def stree10RLRRLLRLR (i : Nat) : State := match i with | 0 => state10_2759 | 1 => state10_2760 | 2 => state10_2761 | 3 => state10_2762 | 4 => state10_2763 | 5 => state10_2764 | 6 => state10_2765 | _ => state10_2766

def stree10RLRRLLRL (i : Nat) : State := if i < 7 then stree10RLRRLLRLL i else stree10RLRRLLRLR (i - 7)

def stree10RLRRLLRRL (i : Nat) : State := match i with | 0 => state10_2767 | 1 => state10_2768 | 2 => state10_2769 | 3 => state10_2770 | 4 => state10_2771 | 5 => state10_2772 | 6 => state10_2773 | _ => state10_2774

def stree10RLRRLLRRR (i : Nat) : State := match i with | 0 => state10_2775 | 1 => state10_2776 | 2 => state10_2777 | 3 => state10_2778 | 4 => state10_2779 | 5 => state10_2780 | 6 => state10_2781 | _ => state10_2782

def stree10RLRRLLRR (i : Nat) : State := if i < 8 then stree10RLRRLLRRL i else stree10RLRRLLRRR (i - 8)

def stree10RLRRLLR (i : Nat) : State := if i < 15 then stree10RLRRLLRL i else stree10RLRRLLRR (i - 15)

def stree10RLRRLL (i : Nat) : State := if i < 31 then stree10RLRRLLL i else stree10RLRRLLR (i - 31)

def stree10RLRRLRLLL (i : Nat) : State := match i with | 0 => state10_2783 | 1 => state10_2784 | 2 => state10_2785 | 3 => state10_2786 | 4 => state10_2787 | 5 => state10_2788 | _ => state10_2789

def stree10RLRRLRLLR (i : Nat) : State := match i with | 0 => state10_2790 | 1 => state10_2791 | 2 => state10_2792 | 3 => state10_2793 | 4 => state10_2794 | 5 => state10_2795 | 6 => state10_2796 | _ => state10_2797

def stree10RLRRLRLL (i : Nat) : State := if i < 7 then stree10RLRRLRLLL i else stree10RLRRLRLLR (i - 7)

def stree10RLRRLRLRL (i : Nat) : State := match i with | 0 => state10_2798 | 1 => state10_2799 | 2 => state10_2800 | 3 => state10_2801 | 4 => state10_2802 | 5 => state10_2803 | 6 => state10_2804 | _ => state10_2805

def stree10RLRRLRLRR (i : Nat) : State := match i with | 0 => state10_2806 | 1 => state10_2807 | 2 => state10_2808 | 3 => state10_2809 | 4 => state10_2810 | 5 => state10_2811 | 6 => state10_2812 | _ => state10_2813

def stree10RLRRLRLR (i : Nat) : State := if i < 8 then stree10RLRRLRLRL i else stree10RLRRLRLRR (i - 8)

def stree10RLRRLRL (i : Nat) : State := if i < 15 then stree10RLRRLRLL i else stree10RLRRLRLR (i - 15)

def stree10RLRRLRRLL (i : Nat) : State := match i with | 0 => state10_2814 | 1 => state10_2815 | 2 => state10_2816 | 3 => state10_2817 | 4 => state10_2818 | 5 => state10_2819 | _ => state10_2820

def stree10RLRRLRRLR (i : Nat) : State := match i with | 0 => state10_2821 | 1 => state10_2822 | 2 => state10_2823 | 3 => state10_2824 | 4 => state10_2825 | 5 => state10_2826 | 6 => state10_2827 | _ => state10_2828

def stree10RLRRLRRL (i : Nat) : State := if i < 7 then stree10RLRRLRRLL i else stree10RLRRLRRLR (i - 7)

def stree10RLRRLRRRL (i : Nat) : State := match i with | 0 => state10_2829 | 1 => state10_2830 | 2 => state10_2831 | 3 => state10_2832 | 4 => state10_2833 | 5 => state10_2834 | 6 => state10_2835 | _ => state10_2836

def stree10RLRRLRRRR (i : Nat) : State := match i with | 0 => state10_2837 | 1 => state10_2838 | 2 => state10_2839 | 3 => state10_2840 | 4 => state10_2841 | 5 => state10_2842 | 6 => state10_2843 | _ => state10_2844

def stree10RLRRLRRR (i : Nat) : State := if i < 8 then stree10RLRRLRRRL i else stree10RLRRLRRRR (i - 8)

def stree10RLRRLRR (i : Nat) : State := if i < 15 then stree10RLRRLRRL i else stree10RLRRLRRR (i - 15)

def stree10RLRRLR (i : Nat) : State := if i < 31 then stree10RLRRLRL i else stree10RLRRLRR (i - 31)

def stree10RLRRL (i : Nat) : State := if i < 62 then stree10RLRRLL i else stree10RLRRLR (i - 62)

def stree10RLRRRLLLL (i : Nat) : State := match i with | 0 => state10_2845 | 1 => state10_2846 | 2 => state10_2847 | 3 => state10_2848 | 4 => state10_2849 | 5 => state10_2850 | _ => state10_2851

def stree10RLRRRLLLR (i : Nat) : State := match i with | 0 => state10_2852 | 1 => state10_2853 | 2 => state10_2854 | 3 => state10_2855 | 4 => state10_2856 | 5 => state10_2857 | 6 => state10_2858 | _ => state10_2859

def stree10RLRRRLLL (i : Nat) : State := if i < 7 then stree10RLRRRLLLL i else stree10RLRRRLLLR (i - 7)

def stree10RLRRRLLRL (i : Nat) : State := match i with | 0 => state10_2860 | 1 => state10_2861 | 2 => state10_2862 | 3 => state10_2863 | 4 => state10_2864 | 5 => state10_2865 | 6 => state10_2866 | _ => state10_2867

def stree10RLRRRLLRR (i : Nat) : State := match i with | 0 => state10_2868 | 1 => state10_2869 | 2 => state10_2870 | 3 => state10_2871 | 4 => state10_2872 | 5 => state10_2873 | 6 => state10_2874 | _ => state10_2875

def stree10RLRRRLLR (i : Nat) : State := if i < 8 then stree10RLRRRLLRL i else stree10RLRRRLLRR (i - 8)

def stree10RLRRRLL (i : Nat) : State := if i < 15 then stree10RLRRRLLL i else stree10RLRRRLLR (i - 15)

def stree10RLRRRLRLL (i : Nat) : State := match i with | 0 => state10_2876 | 1 => state10_2877 | 2 => state10_2878 | 3 => state10_2879 | 4 => state10_2880 | 5 => state10_2881 | _ => state10_2882

def stree10RLRRRLRLR (i : Nat) : State := match i with | 0 => state10_2883 | 1 => state10_2884 | 2 => state10_2885 | 3 => state10_2886 | 4 => state10_2887 | 5 => state10_2888 | 6 => state10_2889 | _ => state10_2890

def stree10RLRRRLRL (i : Nat) : State := if i < 7 then stree10RLRRRLRLL i else stree10RLRRRLRLR (i - 7)

def stree10RLRRRLRRL (i : Nat) : State := match i with | 0 => state10_2891 | 1 => state10_2892 | 2 => state10_2893 | 3 => state10_2894 | 4 => state10_2895 | 5 => state10_2896 | 6 => state10_2897 | _ => state10_2898

def stree10RLRRRLRRR (i : Nat) : State := match i with | 0 => state10_2899 | 1 => state10_2900 | 2 => state10_2901 | 3 => state10_2902 | 4 => state10_2903 | 5 => state10_2904 | 6 => state10_2905 | _ => state10_2906

def stree10RLRRRLRR (i : Nat) : State := if i < 8 then stree10RLRRRLRRL i else stree10RLRRRLRRR (i - 8)

def stree10RLRRRLR (i : Nat) : State := if i < 15 then stree10RLRRRLRL i else stree10RLRRRLRR (i - 15)

def stree10RLRRRL (i : Nat) : State := if i < 31 then stree10RLRRRLL i else stree10RLRRRLR (i - 31)

def stree10RLRRRRLLL (i : Nat) : State := match i with | 0 => state10_2907 | 1 => state10_2908 | 2 => state10_2909 | 3 => state10_2910 | 4 => state10_2911 | 5 => state10_2912 | _ => state10_2913

def stree10RLRRRRLLR (i : Nat) : State := match i with | 0 => state10_2914 | 1 => state10_2915 | 2 => state10_2916 | 3 => state10_2917 | 4 => state10_2918 | 5 => state10_2919 | 6 => state10_2920 | _ => state10_2921

def stree10RLRRRRLL (i : Nat) : State := if i < 7 then stree10RLRRRRLLL i else stree10RLRRRRLLR (i - 7)

def stree10RLRRRRLRL (i : Nat) : State := match i with | 0 => state10_2922 | 1 => state10_2923 | 2 => state10_2924 | 3 => state10_2925 | 4 => state10_2926 | 5 => state10_2927 | 6 => state10_2928 | _ => state10_2929

def stree10RLRRRRLRR (i : Nat) : State := match i with | 0 => state10_2930 | 1 => state10_2931 | 2 => state10_2932 | 3 => state10_2933 | 4 => state10_2934 | 5 => state10_2935 | 6 => state10_2936 | _ => state10_2937

def stree10RLRRRRLR (i : Nat) : State := if i < 8 then stree10RLRRRRLRL i else stree10RLRRRRLRR (i - 8)

def stree10RLRRRRL (i : Nat) : State := if i < 15 then stree10RLRRRRLL i else stree10RLRRRRLR (i - 15)

def stree10RLRRRRRLL (i : Nat) : State := match i with | 0 => state10_2938 | 1 => state10_2939 | 2 => state10_2940 | 3 => state10_2941 | 4 => state10_2942 | 5 => state10_2943 | _ => state10_2944

def stree10RLRRRRRLR (i : Nat) : State := match i with | 0 => state10_2945 | 1 => state10_2946 | 2 => state10_2947 | 3 => state10_2948 | 4 => state10_2949 | 5 => state10_2950 | 6 => state10_2951 | _ => state10_2952

def stree10RLRRRRRL (i : Nat) : State := if i < 7 then stree10RLRRRRRLL i else stree10RLRRRRRLR (i - 7)

def stree10RLRRRRRRL (i : Nat) : State := match i with | 0 => state10_2953 | 1 => state10_2954 | 2 => state10_2955 | 3 => state10_2956 | 4 => state10_2957 | 5 => state10_2958 | 6 => state10_2959 | _ => state10_2960

def stree10RLRRRRRRR (i : Nat) : State := match i with | 0 => state10_2961 | 1 => state10_2962 | 2 => state10_2963 | 3 => state10_2964 | 4 => state10_2965 | 5 => state10_2966 | 6 => state10_2967 | _ => state10_2968

def stree10RLRRRRRR (i : Nat) : State := if i < 8 then stree10RLRRRRRRL i else stree10RLRRRRRRR (i - 8)

def stree10RLRRRRR (i : Nat) : State := if i < 15 then stree10RLRRRRRL i else stree10RLRRRRRR (i - 15)

def stree10RLRRRR (i : Nat) : State := if i < 31 then stree10RLRRRRL i else stree10RLRRRRR (i - 31)

def stree10RLRRR (i : Nat) : State := if i < 62 then stree10RLRRRL i else stree10RLRRRR (i - 62)

def stree10RLRR (i : Nat) : State := if i < 124 then stree10RLRRL i else stree10RLRRR (i - 124)

def stree10RLR (i : Nat) : State := if i < 247 then stree10RLRL i else stree10RLRR (i - 247)

def stree10RL (i : Nat) : State := if i < 495 then stree10RLL i else stree10RLR (i - 495)

def stree10RRLLLLLLL (i : Nat) : State := match i with | 0 => state10_2969 | 1 => state10_2970 | 2 => state10_2971 | 3 => state10_2972 | 4 => state10_2973 | 5 => state10_2974 | _ => state10_2975

def stree10RRLLLLLLR (i : Nat) : State := match i with | 0 => state10_2976 | 1 => state10_2977 | 2 => state10_2978 | 3 => state10_2979 | 4 => state10_2980 | 5 => state10_2981 | 6 => state10_2982 | _ => state10_2983

def stree10RRLLLLLL (i : Nat) : State := if i < 7 then stree10RRLLLLLLL i else stree10RRLLLLLLR (i - 7)

def stree10RRLLLLLRL (i : Nat) : State := match i with | 0 => state10_2984 | 1 => state10_2985 | 2 => state10_2986 | 3 => state10_2987 | 4 => state10_2988 | 5 => state10_2989 | _ => state10_2990

def stree10RRLLLLLRR (i : Nat) : State := match i with | 0 => state10_2991 | 1 => state10_2992 | 2 => state10_2993 | 3 => state10_2994 | 4 => state10_2995 | 5 => state10_2996 | 6 => state10_2997 | _ => state10_2998

def stree10RRLLLLLR (i : Nat) : State := if i < 7 then stree10RRLLLLLRL i else stree10RRLLLLLRR (i - 7)

def stree10RRLLLLL (i : Nat) : State := if i < 15 then stree10RRLLLLLL i else stree10RRLLLLLR (i - 15)

def stree10RRLLLLRLL (i : Nat) : State := match i with | 0 => state10_2999 | 1 => state10_3000 | 2 => state10_3001 | 3 => state10_3002 | 4 => state10_3003 | 5 => state10_3004 | _ => state10_3005

def stree10RRLLLLRLR (i : Nat) : State := match i with | 0 => state10_3006 | 1 => state10_3007 | 2 => state10_3008 | 3 => state10_3009 | 4 => state10_3010 | 5 => state10_3011 | 6 => state10_3012 | _ => state10_3013

def stree10RRLLLLRL (i : Nat) : State := if i < 7 then stree10RRLLLLRLL i else stree10RRLLLLRLR (i - 7)

def stree10RRLLLLRRL (i : Nat) : State := match i with | 0 => state10_3014 | 1 => state10_3015 | 2 => state10_3016 | 3 => state10_3017 | 4 => state10_3018 | 5 => state10_3019 | 6 => state10_3020 | _ => state10_3021

def stree10RRLLLLRRR (i : Nat) : State := match i with | 0 => state10_3022 | 1 => state10_3023 | 2 => state10_3024 | 3 => state10_3025 | 4 => state10_3026 | 5 => state10_3027 | 6 => state10_3028 | _ => state10_3029

def stree10RRLLLLRR (i : Nat) : State := if i < 8 then stree10RRLLLLRRL i else stree10RRLLLLRRR (i - 8)

def stree10RRLLLLR (i : Nat) : State := if i < 15 then stree10RRLLLLRL i else stree10RRLLLLRR (i - 15)

def stree10RRLLLL (i : Nat) : State := if i < 30 then stree10RRLLLLL i else stree10RRLLLLR (i - 30)

def stree10RRLLLRLLL (i : Nat) : State := match i with | 0 => state10_3030 | 1 => state10_3031 | 2 => state10_3032 | 3 => state10_3033 | 4 => state10_3034 | 5 => state10_3035 | _ => state10_3036

def stree10RRLLLRLLR (i : Nat) : State := match i with | 0 => state10_3037 | 1 => state10_3038 | 2 => state10_3039 | 3 => state10_3040 | 4 => state10_3041 | 5 => state10_3042 | 6 => state10_3043 | _ => state10_3044

def stree10RRLLLRLL (i : Nat) : State := if i < 7 then stree10RRLLLRLLL i else stree10RRLLLRLLR (i - 7)

def stree10RRLLLRLRL (i : Nat) : State := match i with | 0 => state10_3045 | 1 => state10_3046 | 2 => state10_3047 | 3 => state10_3048 | 4 => state10_3049 | 5 => state10_3050 | 6 => state10_3051 | _ => state10_3052

def stree10RRLLLRLRR (i : Nat) : State := match i with | 0 => state10_3053 | 1 => state10_3054 | 2 => state10_3055 | 3 => state10_3056 | 4 => state10_3057 | 5 => state10_3058 | 6 => state10_3059 | _ => state10_3060

def stree10RRLLLRLR (i : Nat) : State := if i < 8 then stree10RRLLLRLRL i else stree10RRLLLRLRR (i - 8)

def stree10RRLLLRL (i : Nat) : State := if i < 15 then stree10RRLLLRLL i else stree10RRLLLRLR (i - 15)

def stree10RRLLLRRLL (i : Nat) : State := match i with | 0 => state10_3061 | 1 => state10_3062 | 2 => state10_3063 | 3 => state10_3064 | 4 => state10_3065 | 5 => state10_3066 | _ => state10_3067

def stree10RRLLLRRLR (i : Nat) : State := match i with | 0 => state10_3068 | 1 => state10_3069 | 2 => state10_3070 | 3 => state10_3071 | 4 => state10_3072 | 5 => state10_3073 | 6 => state10_3074 | _ => state10_3075

def stree10RRLLLRRL (i : Nat) : State := if i < 7 then stree10RRLLLRRLL i else stree10RRLLLRRLR (i - 7)

def stree10RRLLLRRRL (i : Nat) : State := match i with | 0 => state10_3076 | 1 => state10_3077 | 2 => state10_3078 | 3 => state10_3079 | 4 => state10_3080 | 5 => state10_3081 | 6 => state10_3082 | _ => state10_3083

def stree10RRLLLRRRR (i : Nat) : State := match i with | 0 => state10_3084 | 1 => state10_3085 | 2 => state10_3086 | 3 => state10_3087 | 4 => state10_3088 | 5 => state10_3089 | 6 => state10_3090 | _ => state10_3091

def stree10RRLLLRRR (i : Nat) : State := if i < 8 then stree10RRLLLRRRL i else stree10RRLLLRRRR (i - 8)

def stree10RRLLLRR (i : Nat) : State := if i < 15 then stree10RRLLLRRL i else stree10RRLLLRRR (i - 15)

def stree10RRLLLR (i : Nat) : State := if i < 31 then stree10RRLLLRL i else stree10RRLLLRR (i - 31)

def stree10RRLLL (i : Nat) : State := if i < 61 then stree10RRLLLL i else stree10RRLLLR (i - 61)

def stree10RRLLRLLLL (i : Nat) : State := match i with | 0 => state10_3092 | 1 => state10_3093 | 2 => state10_3094 | 3 => state10_3095 | 4 => state10_3096 | 5 => state10_3097 | _ => state10_3098

def stree10RRLLRLLLR (i : Nat) : State := match i with | 0 => state10_3099 | 1 => state10_3100 | 2 => state10_3101 | 3 => state10_3102 | 4 => state10_3103 | 5 => state10_3104 | 6 => state10_3105 | _ => state10_3106

def stree10RRLLRLLL (i : Nat) : State := if i < 7 then stree10RRLLRLLLL i else stree10RRLLRLLLR (i - 7)

def stree10RRLLRLLRL (i : Nat) : State := match i with | 0 => state10_3107 | 1 => state10_3108 | 2 => state10_3109 | 3 => state10_3110 | 4 => state10_3111 | 5 => state10_3112 | 6 => state10_3113 | _ => state10_3114

def stree10RRLLRLLRR (i : Nat) : State := match i with | 0 => state10_3115 | 1 => state10_3116 | 2 => state10_3117 | 3 => state10_3118 | 4 => state10_3119 | 5 => state10_3120 | 6 => state10_3121 | _ => state10_3122

def stree10RRLLRLLR (i : Nat) : State := if i < 8 then stree10RRLLRLLRL i else stree10RRLLRLLRR (i - 8)

def stree10RRLLRLL (i : Nat) : State := if i < 15 then stree10RRLLRLLL i else stree10RRLLRLLR (i - 15)

def stree10RRLLRLRLL (i : Nat) : State := match i with | 0 => state10_3123 | 1 => state10_3124 | 2 => state10_3125 | 3 => state10_3126 | 4 => state10_3127 | 5 => state10_3128 | _ => state10_3129

def stree10RRLLRLRLR (i : Nat) : State := match i with | 0 => state10_3130 | 1 => state10_3131 | 2 => state10_3132 | 3 => state10_3133 | 4 => state10_3134 | 5 => state10_3135 | 6 => state10_3136 | _ => state10_3137

def stree10RRLLRLRL (i : Nat) : State := if i < 7 then stree10RRLLRLRLL i else stree10RRLLRLRLR (i - 7)

def stree10RRLLRLRRL (i : Nat) : State := match i with | 0 => state10_3138 | 1 => state10_3139 | 2 => state10_3140 | 3 => state10_3141 | 4 => state10_3142 | 5 => state10_3143 | 6 => state10_3144 | _ => state10_3145

def stree10RRLLRLRRR (i : Nat) : State := match i with | 0 => state10_3146 | 1 => state10_3147 | 2 => state10_3148 | 3 => state10_3149 | 4 => state10_3150 | 5 => state10_3151 | 6 => state10_3152 | _ => state10_3153

def stree10RRLLRLRR (i : Nat) : State := if i < 8 then stree10RRLLRLRRL i else stree10RRLLRLRRR (i - 8)

def stree10RRLLRLR (i : Nat) : State := if i < 15 then stree10RRLLRLRL i else stree10RRLLRLRR (i - 15)

def stree10RRLLRL (i : Nat) : State := if i < 31 then stree10RRLLRLL i else stree10RRLLRLR (i - 31)

def stree10RRLLRRLLL (i : Nat) : State := match i with | 0 => state10_3154 | 1 => state10_3155 | 2 => state10_3156 | 3 => state10_3157 | 4 => state10_3158 | 5 => state10_3159 | _ => state10_3160

def stree10RRLLRRLLR (i : Nat) : State := match i with | 0 => state10_3161 | 1 => state10_3162 | 2 => state10_3163 | 3 => state10_3164 | 4 => state10_3165 | 5 => state10_3166 | 6 => state10_3167 | _ => state10_3168

def stree10RRLLRRLL (i : Nat) : State := if i < 7 then stree10RRLLRRLLL i else stree10RRLLRRLLR (i - 7)

def stree10RRLLRRLRL (i : Nat) : State := match i with | 0 => state10_3169 | 1 => state10_3170 | 2 => state10_3171 | 3 => state10_3172 | 4 => state10_3173 | 5 => state10_3174 | 6 => state10_3175 | _ => state10_3176

def stree10RRLLRRLRR (i : Nat) : State := match i with | 0 => state10_3177 | 1 => state10_3178 | 2 => state10_3179 | 3 => state10_3180 | 4 => state10_3181 | 5 => state10_3182 | 6 => state10_3183 | _ => state10_3184

def stree10RRLLRRLR (i : Nat) : State := if i < 8 then stree10RRLLRRLRL i else stree10RRLLRRLRR (i - 8)

def stree10RRLLRRL (i : Nat) : State := if i < 15 then stree10RRLLRRLL i else stree10RRLLRRLR (i - 15)

def stree10RRLLRRRLL (i : Nat) : State := match i with | 0 => state10_3185 | 1 => state10_3186 | 2 => state10_3187 | 3 => state10_3188 | 4 => state10_3189 | 5 => state10_3190 | _ => state10_3191

def stree10RRLLRRRLR (i : Nat) : State := match i with | 0 => state10_3192 | 1 => state10_3193 | 2 => state10_3194 | 3 => state10_3195 | 4 => state10_3196 | 5 => state10_3197 | 6 => state10_3198 | _ => state10_3199

def stree10RRLLRRRL (i : Nat) : State := if i < 7 then stree10RRLLRRRLL i else stree10RRLLRRRLR (i - 7)

def stree10RRLLRRRRL (i : Nat) : State := match i with | 0 => state10_3200 | 1 => state10_3201 | 2 => state10_3202 | 3 => state10_3203 | 4 => state10_3204 | 5 => state10_3205 | 6 => state10_3206 | _ => state10_3207

def stree10RRLLRRRRR (i : Nat) : State := match i with | 0 => state10_3208 | 1 => state10_3209 | 2 => state10_3210 | 3 => state10_3211 | 4 => state10_3212 | 5 => state10_3213 | 6 => state10_3214 | _ => state10_3215

def stree10RRLLRRRR (i : Nat) : State := if i < 8 then stree10RRLLRRRRL i else stree10RRLLRRRRR (i - 8)

def stree10RRLLRRR (i : Nat) : State := if i < 15 then stree10RRLLRRRL i else stree10RRLLRRRR (i - 15)

def stree10RRLLRR (i : Nat) : State := if i < 31 then stree10RRLLRRL i else stree10RRLLRRR (i - 31)

def stree10RRLLR (i : Nat) : State := if i < 62 then stree10RRLLRL i else stree10RRLLRR (i - 62)

def stree10RRLL (i : Nat) : State := if i < 123 then stree10RRLLL i else stree10RRLLR (i - 123)

def stree10RRLRLLLLL (i : Nat) : State := match i with | 0 => state10_3216 | 1 => state10_3217 | 2 => state10_3218 | 3 => state10_3219 | 4 => state10_3220 | 5 => state10_3221 | _ => state10_3222

def stree10RRLRLLLLR (i : Nat) : State := match i with | 0 => state10_3223 | 1 => state10_3224 | 2 => state10_3225 | 3 => state10_3226 | 4 => state10_3227 | 5 => state10_3228 | 6 => state10_3229 | _ => state10_3230

def stree10RRLRLLLL (i : Nat) : State := if i < 7 then stree10RRLRLLLLL i else stree10RRLRLLLLR (i - 7)

def stree10RRLRLLLRL (i : Nat) : State := match i with | 0 => state10_3231 | 1 => state10_3232 | 2 => state10_3233 | 3 => state10_3234 | 4 => state10_3235 | 5 => state10_3236 | 6 => state10_3237 | _ => state10_3238

def stree10RRLRLLLRR (i : Nat) : State := match i with | 0 => state10_3239 | 1 => state10_3240 | 2 => state10_3241 | 3 => state10_3242 | 4 => state10_3243 | 5 => state10_3244 | 6 => state10_3245 | _ => state10_3246

def stree10RRLRLLLR (i : Nat) : State := if i < 8 then stree10RRLRLLLRL i else stree10RRLRLLLRR (i - 8)

def stree10RRLRLLL (i : Nat) : State := if i < 15 then stree10RRLRLLLL i else stree10RRLRLLLR (i - 15)

def stree10RRLRLLRLL (i : Nat) : State := match i with | 0 => state10_3247 | 1 => state10_3248 | 2 => state10_3249 | 3 => state10_3250 | 4 => state10_3251 | 5 => state10_3252 | _ => state10_3253

def stree10RRLRLLRLR (i : Nat) : State := match i with | 0 => state10_3254 | 1 => state10_3255 | 2 => state10_3256 | 3 => state10_3257 | 4 => state10_3258 | 5 => state10_3259 | 6 => state10_3260 | _ => state10_3261

def stree10RRLRLLRL (i : Nat) : State := if i < 7 then stree10RRLRLLRLL i else stree10RRLRLLRLR (i - 7)

def stree10RRLRLLRRL (i : Nat) : State := match i with | 0 => state10_3262 | 1 => state10_3263 | 2 => state10_3264 | 3 => state10_3265 | 4 => state10_3266 | 5 => state10_3267 | 6 => state10_3268 | _ => state10_3269

def stree10RRLRLLRRR (i : Nat) : State := match i with | 0 => state10_3270 | 1 => state10_3271 | 2 => state10_3272 | 3 => state10_3273 | 4 => state10_3274 | 5 => state10_3275 | 6 => state10_3276 | _ => state10_3277

def stree10RRLRLLRR (i : Nat) : State := if i < 8 then stree10RRLRLLRRL i else stree10RRLRLLRRR (i - 8)

def stree10RRLRLLR (i : Nat) : State := if i < 15 then stree10RRLRLLRL i else stree10RRLRLLRR (i - 15)

def stree10RRLRLL (i : Nat) : State := if i < 31 then stree10RRLRLLL i else stree10RRLRLLR (i - 31)

def stree10RRLRLRLLL (i : Nat) : State := match i with | 0 => state10_3278 | 1 => state10_3279 | 2 => state10_3280 | 3 => state10_3281 | 4 => state10_3282 | 5 => state10_3283 | _ => state10_3284

def stree10RRLRLRLLR (i : Nat) : State := match i with | 0 => state10_3285 | 1 => state10_3286 | 2 => state10_3287 | 3 => state10_3288 | 4 => state10_3289 | 5 => state10_3290 | 6 => state10_3291 | _ => state10_3292

def stree10RRLRLRLL (i : Nat) : State := if i < 7 then stree10RRLRLRLLL i else stree10RRLRLRLLR (i - 7)

def stree10RRLRLRLRL (i : Nat) : State := match i with | 0 => state10_3293 | 1 => state10_3294 | 2 => state10_3295 | 3 => state10_3296 | 4 => state10_3297 | 5 => state10_3298 | 6 => state10_3299 | _ => state10_3300

def stree10RRLRLRLRR (i : Nat) : State := match i with | 0 => state10_3301 | 1 => state10_3302 | 2 => state10_3303 | 3 => state10_3304 | 4 => state10_3305 | 5 => state10_3306 | 6 => state10_3307 | _ => state10_3308

def stree10RRLRLRLR (i : Nat) : State := if i < 8 then stree10RRLRLRLRL i else stree10RRLRLRLRR (i - 8)

def stree10RRLRLRL (i : Nat) : State := if i < 15 then stree10RRLRLRLL i else stree10RRLRLRLR (i - 15)

def stree10RRLRLRRLL (i : Nat) : State := match i with | 0 => state10_3309 | 1 => state10_3310 | 2 => state10_3311 | 3 => state10_3312 | 4 => state10_3313 | 5 => state10_3314 | _ => state10_3315

def stree10RRLRLRRLR (i : Nat) : State := match i with | 0 => state10_3316 | 1 => state10_3317 | 2 => state10_3318 | 3 => state10_3319 | 4 => state10_3320 | 5 => state10_3321 | 6 => state10_3322 | _ => state10_3323

def stree10RRLRLRRL (i : Nat) : State := if i < 7 then stree10RRLRLRRLL i else stree10RRLRLRRLR (i - 7)

def stree10RRLRLRRRL (i : Nat) : State := match i with | 0 => state10_3324 | 1 => state10_3325 | 2 => state10_3326 | 3 => state10_3327 | 4 => state10_3328 | 5 => state10_3329 | 6 => state10_3330 | _ => state10_3331

def stree10RRLRLRRRR (i : Nat) : State := match i with | 0 => state10_3332 | 1 => state10_3333 | 2 => state10_3334 | 3 => state10_3335 | 4 => state10_3336 | 5 => state10_3337 | 6 => state10_3338 | _ => state10_3339

def stree10RRLRLRRR (i : Nat) : State := if i < 8 then stree10RRLRLRRRL i else stree10RRLRLRRRR (i - 8)

def stree10RRLRLRR (i : Nat) : State := if i < 15 then stree10RRLRLRRL i else stree10RRLRLRRR (i - 15)

def stree10RRLRLR (i : Nat) : State := if i < 31 then stree10RRLRLRL i else stree10RRLRLRR (i - 31)

def stree10RRLRL (i : Nat) : State := if i < 62 then stree10RRLRLL i else stree10RRLRLR (i - 62)

def stree10RRLRRLLLL (i : Nat) : State := match i with | 0 => state10_3340 | 1 => state10_3341 | 2 => state10_3342 | 3 => state10_3343 | 4 => state10_3344 | 5 => state10_3345 | _ => state10_3346

def stree10RRLRRLLLR (i : Nat) : State := match i with | 0 => state10_3347 | 1 => state10_3348 | 2 => state10_3349 | 3 => state10_3350 | 4 => state10_3351 | 5 => state10_3352 | 6 => state10_3353 | _ => state10_3354

def stree10RRLRRLLL (i : Nat) : State := if i < 7 then stree10RRLRRLLLL i else stree10RRLRRLLLR (i - 7)

def stree10RRLRRLLRL (i : Nat) : State := match i with | 0 => state10_3355 | 1 => state10_3356 | 2 => state10_3357 | 3 => state10_3358 | 4 => state10_3359 | 5 => state10_3360 | 6 => state10_3361 | _ => state10_3362

def stree10RRLRRLLRR (i : Nat) : State := match i with | 0 => state10_3363 | 1 => state10_3364 | 2 => state10_3365 | 3 => state10_3366 | 4 => state10_3367 | 5 => state10_3368 | 6 => state10_3369 | _ => state10_3370

def stree10RRLRRLLR (i : Nat) : State := if i < 8 then stree10RRLRRLLRL i else stree10RRLRRLLRR (i - 8)

def stree10RRLRRLL (i : Nat) : State := if i < 15 then stree10RRLRRLLL i else stree10RRLRRLLR (i - 15)

def stree10RRLRRLRLL (i : Nat) : State := match i with | 0 => state10_3371 | 1 => state10_3372 | 2 => state10_3373 | 3 => state10_3374 | 4 => state10_3375 | 5 => state10_3376 | _ => state10_3377

def stree10RRLRRLRLR (i : Nat) : State := match i with | 0 => state10_3378 | 1 => state10_3379 | 2 => state10_3380 | 3 => state10_3381 | 4 => state10_3382 | 5 => state10_3383 | 6 => state10_3384 | _ => state10_3385

def stree10RRLRRLRL (i : Nat) : State := if i < 7 then stree10RRLRRLRLL i else stree10RRLRRLRLR (i - 7)

def stree10RRLRRLRRL (i : Nat) : State := match i with | 0 => state10_3386 | 1 => state10_3387 | 2 => state10_3388 | 3 => state10_3389 | 4 => state10_3390 | 5 => state10_3391 | 6 => state10_3392 | _ => state10_3393

def stree10RRLRRLRRR (i : Nat) : State := match i with | 0 => state10_3394 | 1 => state10_3395 | 2 => state10_3396 | 3 => state10_3397 | 4 => state10_3398 | 5 => state10_3399 | 6 => state10_3400 | _ => state10_3401

def stree10RRLRRLRR (i : Nat) : State := if i < 8 then stree10RRLRRLRRL i else stree10RRLRRLRRR (i - 8)

def stree10RRLRRLR (i : Nat) : State := if i < 15 then stree10RRLRRLRL i else stree10RRLRRLRR (i - 15)

def stree10RRLRRL (i : Nat) : State := if i < 31 then stree10RRLRRLL i else stree10RRLRRLR (i - 31)

def stree10RRLRRRLLL (i : Nat) : State := match i with | 0 => state10_3402 | 1 => state10_3403 | 2 => state10_3404 | 3 => state10_3405 | 4 => state10_3406 | 5 => state10_3407 | _ => state10_3408

def stree10RRLRRRLLR (i : Nat) : State := match i with | 0 => state10_3409 | 1 => state10_3410 | 2 => state10_3411 | 3 => state10_3412 | 4 => state10_3413 | 5 => state10_3414 | 6 => state10_3415 | _ => state10_3416

def stree10RRLRRRLL (i : Nat) : State := if i < 7 then stree10RRLRRRLLL i else stree10RRLRRRLLR (i - 7)

def stree10RRLRRRLRL (i : Nat) : State := match i with | 0 => state10_3417 | 1 => state10_3418 | 2 => state10_3419 | 3 => state10_3420 | 4 => state10_3421 | 5 => state10_3422 | 6 => state10_3423 | _ => state10_3424

def stree10RRLRRRLRR (i : Nat) : State := match i with | 0 => state10_3425 | 1 => state10_3426 | 2 => state10_3427 | 3 => state10_3428 | 4 => state10_3429 | 5 => state10_3430 | 6 => state10_3431 | _ => state10_3432

def stree10RRLRRRLR (i : Nat) : State := if i < 8 then stree10RRLRRRLRL i else stree10RRLRRRLRR (i - 8)

def stree10RRLRRRL (i : Nat) : State := if i < 15 then stree10RRLRRRLL i else stree10RRLRRRLR (i - 15)

def stree10RRLRRRRLL (i : Nat) : State := match i with | 0 => state10_3433 | 1 => state10_3434 | 2 => state10_3435 | 3 => state10_3436 | 4 => state10_3437 | 5 => state10_3438 | _ => state10_3439

def stree10RRLRRRRLR (i : Nat) : State := match i with | 0 => state10_3440 | 1 => state10_3441 | 2 => state10_3442 | 3 => state10_3443 | 4 => state10_3444 | 5 => state10_3445 | 6 => state10_3446 | _ => state10_3447

def stree10RRLRRRRL (i : Nat) : State := if i < 7 then stree10RRLRRRRLL i else stree10RRLRRRRLR (i - 7)

def stree10RRLRRRRRL (i : Nat) : State := match i with | 0 => state10_3448 | 1 => state10_3449 | 2 => state10_3450 | 3 => state10_3451 | 4 => state10_3452 | 5 => state10_3453 | 6 => state10_3454 | _ => state10_3455

def stree10RRLRRRRRR (i : Nat) : State := match i with | 0 => state10_3456 | 1 => state10_3457 | 2 => state10_3458 | 3 => state10_3459 | 4 => state10_3460 | 5 => state10_3461 | 6 => state10_3462 | _ => state10_3463

def stree10RRLRRRRR (i : Nat) : State := if i < 8 then stree10RRLRRRRRL i else stree10RRLRRRRRR (i - 8)

def stree10RRLRRRR (i : Nat) : State := if i < 15 then stree10RRLRRRRL i else stree10RRLRRRRR (i - 15)

def stree10RRLRRR (i : Nat) : State := if i < 31 then stree10RRLRRRL i else stree10RRLRRRR (i - 31)

def stree10RRLRR (i : Nat) : State := if i < 62 then stree10RRLRRL i else stree10RRLRRR (i - 62)

def stree10RRLR (i : Nat) : State := if i < 124 then stree10RRLRL i else stree10RRLRR (i - 124)

def stree10RRL (i : Nat) : State := if i < 247 then stree10RRLL i else stree10RRLR (i - 247)

def stree10RRRLLLLLL (i : Nat) : State := match i with | 0 => state10_3464 | 1 => state10_3465 | 2 => state10_3466 | 3 => state10_3467 | 4 => state10_3468 | 5 => state10_3469 | _ => state10_3470

def stree10RRRLLLLLR (i : Nat) : State := match i with | 0 => state10_3471 | 1 => state10_3472 | 2 => state10_3473 | 3 => state10_3474 | 4 => state10_3475 | 5 => state10_3476 | 6 => state10_3477 | _ => state10_3478

def stree10RRRLLLLL (i : Nat) : State := if i < 7 then stree10RRRLLLLLL i else stree10RRRLLLLLR (i - 7)

def stree10RRRLLLLRL (i : Nat) : State := match i with | 0 => state10_3479 | 1 => state10_3480 | 2 => state10_3481 | 3 => state10_3482 | 4 => state10_3483 | 5 => state10_3484 | _ => state10_3485

def stree10RRRLLLLRR (i : Nat) : State := match i with | 0 => state10_3486 | 1 => state10_3487 | 2 => state10_3488 | 3 => state10_3489 | 4 => state10_3490 | 5 => state10_3491 | 6 => state10_3492 | _ => state10_3493

def stree10RRRLLLLR (i : Nat) : State := if i < 7 then stree10RRRLLLLRL i else stree10RRRLLLLRR (i - 7)

def stree10RRRLLLL (i : Nat) : State := if i < 15 then stree10RRRLLLLL i else stree10RRRLLLLR (i - 15)

def stree10RRRLLLRLL (i : Nat) : State := match i with | 0 => state10_3494 | 1 => state10_3495 | 2 => state10_3496 | 3 => state10_3497 | 4 => state10_3498 | 5 => state10_3499 | _ => state10_3500

def stree10RRRLLLRLR (i : Nat) : State := match i with | 0 => state10_3501 | 1 => state10_3502 | 2 => state10_3503 | 3 => state10_3504 | 4 => state10_3505 | 5 => state10_3506 | 6 => state10_3507 | _ => state10_3508

def stree10RRRLLLRL (i : Nat) : State := if i < 7 then stree10RRRLLLRLL i else stree10RRRLLLRLR (i - 7)

def stree10RRRLLLRRL (i : Nat) : State := match i with | 0 => state10_3509 | 1 => state10_3510 | 2 => state10_3511 | 3 => state10_3512 | 4 => state10_3513 | 5 => state10_3514 | 6 => state10_3515 | _ => state10_3516

def stree10RRRLLLRRR (i : Nat) : State := match i with | 0 => state10_3517 | 1 => state10_3518 | 2 => state10_3519 | 3 => state10_3520 | 4 => state10_3521 | 5 => state10_3522 | 6 => state10_3523 | _ => state10_3524

def stree10RRRLLLRR (i : Nat) : State := if i < 8 then stree10RRRLLLRRL i else stree10RRRLLLRRR (i - 8)

def stree10RRRLLLR (i : Nat) : State := if i < 15 then stree10RRRLLLRL i else stree10RRRLLLRR (i - 15)

def stree10RRRLLL (i : Nat) : State := if i < 30 then stree10RRRLLLL i else stree10RRRLLLR (i - 30)

def stree10RRRLLRLLL (i : Nat) : State := match i with | 0 => state10_3525 | 1 => state10_3526 | 2 => state10_3527 | 3 => state10_3528 | 4 => state10_3529 | 5 => state10_3530 | _ => state10_3531

def stree10RRRLLRLLR (i : Nat) : State := match i with | 0 => state10_3532 | 1 => state10_3533 | 2 => state10_3534 | 3 => state10_3535 | 4 => state10_3536 | 5 => state10_3537 | 6 => state10_3538 | _ => state10_3539

def stree10RRRLLRLL (i : Nat) : State := if i < 7 then stree10RRRLLRLLL i else stree10RRRLLRLLR (i - 7)

def stree10RRRLLRLRL (i : Nat) : State := match i with | 0 => state10_3540 | 1 => state10_3541 | 2 => state10_3542 | 3 => state10_3543 | 4 => state10_3544 | 5 => state10_3545 | 6 => state10_3546 | _ => state10_3547

def stree10RRRLLRLRR (i : Nat) : State := match i with | 0 => state10_3548 | 1 => state10_3549 | 2 => state10_3550 | 3 => state10_3551 | 4 => state10_3552 | 5 => state10_3553 | 6 => state10_3554 | _ => state10_3555

def stree10RRRLLRLR (i : Nat) : State := if i < 8 then stree10RRRLLRLRL i else stree10RRRLLRLRR (i - 8)

def stree10RRRLLRL (i : Nat) : State := if i < 15 then stree10RRRLLRLL i else stree10RRRLLRLR (i - 15)

def stree10RRRLLRRLL (i : Nat) : State := match i with | 0 => state10_3556 | 1 => state10_3557 | 2 => state10_3558 | 3 => state10_3559 | 4 => state10_3560 | 5 => state10_3561 | _ => state10_3562

def stree10RRRLLRRLR (i : Nat) : State := match i with | 0 => state10_3563 | 1 => state10_3564 | 2 => state10_3565 | 3 => state10_3566 | 4 => state10_3567 | 5 => state10_3568 | 6 => state10_3569 | _ => state10_3570

def stree10RRRLLRRL (i : Nat) : State := if i < 7 then stree10RRRLLRRLL i else stree10RRRLLRRLR (i - 7)

def stree10RRRLLRRRL (i : Nat) : State := match i with | 0 => state10_3571 | 1 => state10_3572 | 2 => state10_3573 | 3 => state10_3574 | 4 => state10_3575 | 5 => state10_3576 | 6 => state10_3577 | _ => state10_3578

def stree10RRRLLRRRR (i : Nat) : State := match i with | 0 => state10_3579 | 1 => state10_3580 | 2 => state10_3581 | 3 => state10_3582 | 4 => state10_3583 | 5 => state10_3584 | 6 => state10_3585 | _ => state10_3586

def stree10RRRLLRRR (i : Nat) : State := if i < 8 then stree10RRRLLRRRL i else stree10RRRLLRRRR (i - 8)

def stree10RRRLLRR (i : Nat) : State := if i < 15 then stree10RRRLLRRL i else stree10RRRLLRRR (i - 15)

def stree10RRRLLR (i : Nat) : State := if i < 31 then stree10RRRLLRL i else stree10RRRLLRR (i - 31)

def stree10RRRLL (i : Nat) : State := if i < 61 then stree10RRRLLL i else stree10RRRLLR (i - 61)

def stree10RRRLRLLLL (i : Nat) : State := match i with | 0 => state10_3587 | 1 => state10_3588 | 2 => state10_3589 | 3 => state10_3590 | 4 => state10_3591 | 5 => state10_3592 | _ => state10_3593

def stree10RRRLRLLLR (i : Nat) : State := match i with | 0 => state10_3594 | 1 => state10_3595 | 2 => state10_3596 | 3 => state10_3597 | 4 => state10_3598 | 5 => state10_3599 | 6 => state10_3600 | _ => state10_3601

def stree10RRRLRLLL (i : Nat) : State := if i < 7 then stree10RRRLRLLLL i else stree10RRRLRLLLR (i - 7)

def stree10RRRLRLLRL (i : Nat) : State := match i with | 0 => state10_3602 | 1 => state10_3603 | 2 => state10_3604 | 3 => state10_3605 | 4 => state10_3606 | 5 => state10_3607 | 6 => state10_3608 | _ => state10_3609

def stree10RRRLRLLRR (i : Nat) : State := match i with | 0 => state10_3610 | 1 => state10_3611 | 2 => state10_3612 | 3 => state10_3613 | 4 => state10_3614 | 5 => state10_3615 | 6 => state10_3616 | _ => state10_3617

def stree10RRRLRLLR (i : Nat) : State := if i < 8 then stree10RRRLRLLRL i else stree10RRRLRLLRR (i - 8)

def stree10RRRLRLL (i : Nat) : State := if i < 15 then stree10RRRLRLLL i else stree10RRRLRLLR (i - 15)

def stree10RRRLRLRLL (i : Nat) : State := match i with | 0 => state10_3618 | 1 => state10_3619 | 2 => state10_3620 | 3 => state10_3621 | 4 => state10_3622 | 5 => state10_3623 | _ => state10_3624

def stree10RRRLRLRLR (i : Nat) : State := match i with | 0 => state10_3625 | 1 => state10_3626 | 2 => state10_3627 | 3 => state10_3628 | 4 => state10_3629 | 5 => state10_3630 | 6 => state10_3631 | _ => state10_3632

def stree10RRRLRLRL (i : Nat) : State := if i < 7 then stree10RRRLRLRLL i else stree10RRRLRLRLR (i - 7)

def stree10RRRLRLRRL (i : Nat) : State := match i with | 0 => state10_3633 | 1 => state10_3634 | 2 => state10_3635 | 3 => state10_3636 | 4 => state10_3637 | 5 => state10_3638 | 6 => state10_3639 | _ => state10_3640

def stree10RRRLRLRRR (i : Nat) : State := match i with | 0 => state10_3641 | 1 => state10_3642 | 2 => state10_3643 | 3 => state10_3644 | 4 => state10_3645 | 5 => state10_3646 | 6 => state10_3647 | _ => state10_3648

def stree10RRRLRLRR (i : Nat) : State := if i < 8 then stree10RRRLRLRRL i else stree10RRRLRLRRR (i - 8)

def stree10RRRLRLR (i : Nat) : State := if i < 15 then stree10RRRLRLRL i else stree10RRRLRLRR (i - 15)

def stree10RRRLRL (i : Nat) : State := if i < 31 then stree10RRRLRLL i else stree10RRRLRLR (i - 31)

def stree10RRRLRRLLL (i : Nat) : State := match i with | 0 => state10_3649 | 1 => state10_3650 | 2 => state10_3651 | 3 => state10_3652 | 4 => state10_3653 | 5 => state10_3654 | _ => state10_3655

def stree10RRRLRRLLR (i : Nat) : State := match i with | 0 => state10_3656 | 1 => state10_3657 | 2 => state10_3658 | 3 => state10_3659 | 4 => state10_3660 | 5 => state10_3661 | 6 => state10_3662 | _ => state10_3663

def stree10RRRLRRLL (i : Nat) : State := if i < 7 then stree10RRRLRRLLL i else stree10RRRLRRLLR (i - 7)

def stree10RRRLRRLRL (i : Nat) : State := match i with | 0 => state10_3664 | 1 => state10_3665 | 2 => state10_3666 | 3 => state10_3667 | 4 => state10_3668 | 5 => state10_3669 | 6 => state10_3670 | _ => state10_3671

def stree10RRRLRRLRR (i : Nat) : State := match i with | 0 => state10_3672 | 1 => state10_3673 | 2 => state10_3674 | 3 => state10_3675 | 4 => state10_3676 | 5 => state10_3677 | 6 => state10_3678 | _ => state10_3679

def stree10RRRLRRLR (i : Nat) : State := if i < 8 then stree10RRRLRRLRL i else stree10RRRLRRLRR (i - 8)

def stree10RRRLRRL (i : Nat) : State := if i < 15 then stree10RRRLRRLL i else stree10RRRLRRLR (i - 15)

def stree10RRRLRRRLL (i : Nat) : State := match i with | 0 => state10_3680 | 1 => state10_3681 | 2 => state10_3682 | 3 => state10_3683 | 4 => state10_3684 | 5 => state10_3685 | _ => state10_3686

def stree10RRRLRRRLR (i : Nat) : State := match i with | 0 => state10_3687 | 1 => state10_3688 | 2 => state10_3689 | 3 => state10_3690 | 4 => state10_3691 | 5 => state10_3692 | 6 => state10_3693 | _ => state10_3694

def stree10RRRLRRRL (i : Nat) : State := if i < 7 then stree10RRRLRRRLL i else stree10RRRLRRRLR (i - 7)

def stree10RRRLRRRRL (i : Nat) : State := match i with | 0 => state10_3695 | 1 => state10_3696 | 2 => state10_3697 | 3 => state10_3698 | 4 => state10_3699 | 5 => state10_3700 | 6 => state10_3701 | _ => state10_3702

def stree10RRRLRRRRR (i : Nat) : State := match i with | 0 => state10_3703 | 1 => state10_3704 | 2 => state10_3705 | 3 => state10_3706 | 4 => state10_3707 | 5 => state10_3708 | 6 => state10_3709 | _ => state10_3710

def stree10RRRLRRRR (i : Nat) : State := if i < 8 then stree10RRRLRRRRL i else stree10RRRLRRRRR (i - 8)

def stree10RRRLRRR (i : Nat) : State := if i < 15 then stree10RRRLRRRL i else stree10RRRLRRRR (i - 15)

def stree10RRRLRR (i : Nat) : State := if i < 31 then stree10RRRLRRL i else stree10RRRLRRR (i - 31)

def stree10RRRLR (i : Nat) : State := if i < 62 then stree10RRRLRL i else stree10RRRLRR (i - 62)

def stree10RRRL (i : Nat) : State := if i < 123 then stree10RRRLL i else stree10RRRLR (i - 123)

def stree10RRRRLLLLL (i : Nat) : State := match i with | 0 => state10_3711 | 1 => state10_3712 | 2 => state10_3713 | 3 => state10_3714 | 4 => state10_3715 | 5 => state10_3716 | _ => state10_3717

def stree10RRRRLLLLR (i : Nat) : State := match i with | 0 => state10_3718 | 1 => state10_3719 | 2 => state10_3720 | 3 => state10_3721 | 4 => state10_3722 | 5 => state10_3723 | 6 => state10_3724 | _ => state10_3725

def stree10RRRRLLLL (i : Nat) : State := if i < 7 then stree10RRRRLLLLL i else stree10RRRRLLLLR (i - 7)

def stree10RRRRLLLRL (i : Nat) : State := match i with | 0 => state10_3726 | 1 => state10_3727 | 2 => state10_3728 | 3 => state10_3729 | 4 => state10_3730 | 5 => state10_3731 | 6 => state10_3732 | _ => state10_3733

def stree10RRRRLLLRR (i : Nat) : State := match i with | 0 => state10_3734 | 1 => state10_3735 | 2 => state10_3736 | 3 => state10_3737 | 4 => state10_3738 | 5 => state10_3739 | 6 => state10_3740 | _ => state10_3741

def stree10RRRRLLLR (i : Nat) : State := if i < 8 then stree10RRRRLLLRL i else stree10RRRRLLLRR (i - 8)

def stree10RRRRLLL (i : Nat) : State := if i < 15 then stree10RRRRLLLL i else stree10RRRRLLLR (i - 15)

def stree10RRRRLLRLL (i : Nat) : State := match i with | 0 => state10_3742 | 1 => state10_3743 | 2 => state10_3744 | 3 => state10_3745 | 4 => state10_3746 | 5 => state10_3747 | _ => state10_3748

def stree10RRRRLLRLR (i : Nat) : State := match i with | 0 => state10_3749 | 1 => state10_3750 | 2 => state10_3751 | 3 => state10_3752 | 4 => state10_3753 | 5 => state10_3754 | 6 => state10_3755 | _ => state10_3756

def stree10RRRRLLRL (i : Nat) : State := if i < 7 then stree10RRRRLLRLL i else stree10RRRRLLRLR (i - 7)

def stree10RRRRLLRRL (i : Nat) : State := match i with | 0 => state10_3757 | 1 => state10_3758 | 2 => state10_3759 | 3 => state10_3760 | 4 => state10_3761 | 5 => state10_3762 | 6 => state10_3763 | _ => state10_3764

def stree10RRRRLLRRR (i : Nat) : State := match i with | 0 => state10_3765 | 1 => state10_3766 | 2 => state10_3767 | 3 => state10_3768 | 4 => state10_3769 | 5 => state10_3770 | 6 => state10_3771 | _ => state10_3772

def stree10RRRRLLRR (i : Nat) : State := if i < 8 then stree10RRRRLLRRL i else stree10RRRRLLRRR (i - 8)

def stree10RRRRLLR (i : Nat) : State := if i < 15 then stree10RRRRLLRL i else stree10RRRRLLRR (i - 15)

def stree10RRRRLL (i : Nat) : State := if i < 31 then stree10RRRRLLL i else stree10RRRRLLR (i - 31)

def stree10RRRRLRLLL (i : Nat) : State := match i with | 0 => state10_3773 | 1 => state10_3774 | 2 => state10_3775 | 3 => state10_3776 | 4 => state10_3777 | 5 => state10_3778 | _ => state10_3779

def stree10RRRRLRLLR (i : Nat) : State := match i with | 0 => state10_3780 | 1 => state10_3781 | 2 => state10_3782 | 3 => state10_3783 | 4 => state10_3784 | 5 => state10_3785 | 6 => state10_3786 | _ => state10_3787

def stree10RRRRLRLL (i : Nat) : State := if i < 7 then stree10RRRRLRLLL i else stree10RRRRLRLLR (i - 7)

def stree10RRRRLRLRL (i : Nat) : State := match i with | 0 => state10_3788 | 1 => state10_3789 | 2 => state10_3790 | 3 => state10_3791 | 4 => state10_3792 | 5 => state10_3793 | 6 => state10_3794 | _ => state10_3795

def stree10RRRRLRLRR (i : Nat) : State := match i with | 0 => state10_3796 | 1 => state10_3797 | 2 => state10_3798 | 3 => state10_3799 | 4 => state10_3800 | 5 => state10_3801 | 6 => state10_3802 | _ => state10_3803

def stree10RRRRLRLR (i : Nat) : State := if i < 8 then stree10RRRRLRLRL i else stree10RRRRLRLRR (i - 8)

def stree10RRRRLRL (i : Nat) : State := if i < 15 then stree10RRRRLRLL i else stree10RRRRLRLR (i - 15)

def stree10RRRRLRRLL (i : Nat) : State := match i with | 0 => state10_3804 | 1 => state10_3805 | 2 => state10_3806 | 3 => state10_3807 | 4 => state10_3808 | 5 => state10_3809 | _ => state10_3810

def stree10RRRRLRRLR (i : Nat) : State := match i with | 0 => state10_3811 | 1 => state10_3812 | 2 => state10_3813 | 3 => state10_3814 | 4 => state10_3815 | 5 => state10_3816 | 6 => state10_3817 | _ => state10_3818

def stree10RRRRLRRL (i : Nat) : State := if i < 7 then stree10RRRRLRRLL i else stree10RRRRLRRLR (i - 7)

def stree10RRRRLRRRL (i : Nat) : State := match i with | 0 => state10_3819 | 1 => state10_3820 | 2 => state10_3821 | 3 => state10_3822 | 4 => state10_3823 | 5 => state10_3824 | 6 => state10_3825 | _ => state10_3826

def stree10RRRRLRRRR (i : Nat) : State := match i with | 0 => state10_3827 | 1 => state10_3828 | 2 => state10_3829 | 3 => state10_3830 | 4 => state10_3831 | 5 => state10_3832 | 6 => state10_3833 | _ => state10_3834

def stree10RRRRLRRR (i : Nat) : State := if i < 8 then stree10RRRRLRRRL i else stree10RRRRLRRRR (i - 8)

def stree10RRRRLRR (i : Nat) : State := if i < 15 then stree10RRRRLRRL i else stree10RRRRLRRR (i - 15)

def stree10RRRRLR (i : Nat) : State := if i < 31 then stree10RRRRLRL i else stree10RRRRLRR (i - 31)

def stree10RRRRL (i : Nat) : State := if i < 62 then stree10RRRRLL i else stree10RRRRLR (i - 62)

def stree10RRRRRLLLL (i : Nat) : State := match i with | 0 => state10_3835 | 1 => state10_3836 | 2 => state10_3837 | 3 => state10_3838 | 4 => state10_3839 | 5 => state10_3840 | _ => state10_3841

def stree10RRRRRLLLR (i : Nat) : State := match i with | 0 => state10_3842 | 1 => state10_3843 | 2 => state10_3844 | 3 => state10_3845 | 4 => state10_3846 | 5 => state10_3847 | 6 => state10_3848 | _ => state10_3849

def stree10RRRRRLLL (i : Nat) : State := if i < 7 then stree10RRRRRLLLL i else stree10RRRRRLLLR (i - 7)

def stree10RRRRRLLRL (i : Nat) : State := match i with | 0 => state10_3850 | 1 => state10_3851 | 2 => state10_3852 | 3 => state10_3853 | 4 => state10_3854 | 5 => state10_3855 | 6 => state10_3856 | _ => state10_3857

def stree10RRRRRLLRR (i : Nat) : State := match i with | 0 => state10_3858 | 1 => state10_3859 | 2 => state10_3860 | 3 => state10_3861 | 4 => state10_3862 | 5 => state10_3863 | 6 => state10_3864 | _ => state10_3865

def stree10RRRRRLLR (i : Nat) : State := if i < 8 then stree10RRRRRLLRL i else stree10RRRRRLLRR (i - 8)

def stree10RRRRRLL (i : Nat) : State := if i < 15 then stree10RRRRRLLL i else stree10RRRRRLLR (i - 15)

def stree10RRRRRLRLL (i : Nat) : State := match i with | 0 => state10_3866 | 1 => state10_3867 | 2 => state10_3868 | 3 => state10_3869 | 4 => state10_3870 | 5 => state10_3871 | _ => state10_3872

def stree10RRRRRLRLR (i : Nat) : State := match i with | 0 => state10_3873 | 1 => state10_3874 | 2 => state10_3875 | 3 => state10_3876 | 4 => state10_3877 | 5 => state10_3878 | 6 => state10_3879 | _ => state10_3880

def stree10RRRRRLRL (i : Nat) : State := if i < 7 then stree10RRRRRLRLL i else stree10RRRRRLRLR (i - 7)

def stree10RRRRRLRRL (i : Nat) : State := match i with | 0 => state10_3881 | 1 => state10_3882 | 2 => state10_3883 | 3 => state10_3884 | 4 => state10_3885 | 5 => state10_3886 | 6 => state10_3887 | _ => state10_3888

def stree10RRRRRLRRR (i : Nat) : State := match i with | 0 => state10_3889 | 1 => state10_3890 | 2 => state10_3891 | 3 => state10_3892 | 4 => state10_3893 | 5 => state10_3894 | 6 => state10_3895 | _ => state10_3896

def stree10RRRRRLRR (i : Nat) : State := if i < 8 then stree10RRRRRLRRL i else stree10RRRRRLRRR (i - 8)

def stree10RRRRRLR (i : Nat) : State := if i < 15 then stree10RRRRRLRL i else stree10RRRRRLRR (i - 15)

def stree10RRRRRL (i : Nat) : State := if i < 31 then stree10RRRRRLL i else stree10RRRRRLR (i - 31)

def stree10RRRRRRLLL (i : Nat) : State := match i with | 0 => state10_3897 | 1 => state10_3898 | 2 => state10_3899 | 3 => state10_3900 | 4 => state10_3901 | 5 => state10_3902 | _ => state10_3903

def stree10RRRRRRLLR (i : Nat) : State := match i with | 0 => state10_3904 | 1 => state10_3905 | 2 => state10_3906 | 3 => state10_3907 | 4 => state10_3908 | 5 => state10_3909 | 6 => state10_3910 | _ => state10_3911

def stree10RRRRRRLL (i : Nat) : State := if i < 7 then stree10RRRRRRLLL i else stree10RRRRRRLLR (i - 7)

def stree10RRRRRRLRL (i : Nat) : State := match i with | 0 => state10_3912 | 1 => state10_3913 | 2 => state10_3914 | 3 => state10_3915 | 4 => state10_3916 | 5 => state10_3917 | 6 => state10_3918 | _ => state10_3919

def stree10RRRRRRLRR (i : Nat) : State := match i with | 0 => state10_3920 | 1 => state10_3921 | 2 => state10_3922 | 3 => state10_3923 | 4 => state10_3924 | 5 => state10_3925 | 6 => state10_3926 | _ => state10_3927

def stree10RRRRRRLR (i : Nat) : State := if i < 8 then stree10RRRRRRLRL i else stree10RRRRRRLRR (i - 8)

def stree10RRRRRRL (i : Nat) : State := if i < 15 then stree10RRRRRRLL i else stree10RRRRRRLR (i - 15)

def stree10RRRRRRRLL (i : Nat) : State := match i with | 0 => state10_3928 | 1 => state10_3929 | 2 => state10_3930 | 3 => state10_3931 | 4 => state10_3932 | 5 => state10_3933 | _ => state10_3934

def stree10RRRRRRRLR (i : Nat) : State := match i with | 0 => state10_3935 | 1 => state10_3936 | 2 => state10_3937 | 3 => state10_3938 | 4 => state10_3939 | 5 => state10_3940 | 6 => state10_3941 | _ => state10_3942

def stree10RRRRRRRL (i : Nat) : State := if i < 7 then stree10RRRRRRRLL i else stree10RRRRRRRLR (i - 7)

def stree10RRRRRRRRL (i : Nat) : State := match i with | 0 => state10_3943 | 1 => state10_3944 | 2 => state10_3945 | 3 => state10_3946 | 4 => state10_3947 | 5 => state10_3948 | 6 => state10_3949 | _ => state10_3950

def stree10RRRRRRRRR (i : Nat) : State := match i with | 0 => state10_3951 | 1 => state10_3952 | 2 => state10_3953 | 3 => state10_3954 | 4 => state10_3955 | 5 => state10_3956 | 6 => state10_3957 | _ => state10_3958

def stree10RRRRRRRR (i : Nat) : State := if i < 8 then stree10RRRRRRRRL i else stree10RRRRRRRRR (i - 8)

def stree10RRRRRRR (i : Nat) : State := if i < 15 then stree10RRRRRRRL i else stree10RRRRRRRR (i - 15)

def stree10RRRRRR (i : Nat) : State := if i < 31 then stree10RRRRRRL i else stree10RRRRRRR (i - 31)

def stree10RRRRR (i : Nat) : State := if i < 62 then stree10RRRRRL i else stree10RRRRRR (i - 62)

def stree10RRRR (i : Nat) : State := if i < 124 then stree10RRRRL i else stree10RRRRR (i - 124)

def stree10RRR (i : Nat) : State := if i < 247 then stree10RRRL i else stree10RRRR (i - 247)

def stree10RR (i : Nat) : State := if i < 495 then stree10RRL i else stree10RRR (i - 495)

def stree10R (i : Nat) : State := if i < 990 then stree10RL i else stree10RR (i - 990)

def stree10 (i : Nat) : State := if i < 1979 then stree10L i else stree10R (i - 1979)

def ntree10LLLLLLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1,by decide⟩,⟨1,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩] | 3 => ![⟨4,by decide⟩,⟨0,by decide⟩,⟨4,by decide⟩] | 4 => ![⟨5,by decide⟩,⟨1,by decide⟩,⟨4,by decide⟩] | 5 => ![⟨6,by decide⟩,⟨2,by decide⟩,⟨7,by decide⟩] | _ => ![⟨8,by decide⟩,⟨9,by decide⟩,⟨8,by decide⟩]

def ntree10LLLLLLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨10,by decide⟩,⟨11,by decide⟩,⟨8,by decide⟩] | 1 => ![⟨12,by decide⟩,⟨13,by decide⟩,⟨14,by decide⟩] | 2 => ![⟨3,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 3 => ![⟨7,by decide⟩,⟨3,by decide⟩,⟨7,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨15,by decide⟩,⟨14,by decide⟩] | 5 => ![⟨9,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | 6 => ![⟨11,by decide⟩,⟨11,by decide⟩,⟨9,by decide⟩] | _ => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨15,by decide⟩]

def ntree10LLLLLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LLLLLLLLL i else ntree10LLLLLLLLR (i - 7)

def ntree10LLLLLLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨16,by decide⟩,⟨3,by decide⟩,⟨16,by decide⟩] | 1 => ![⟨17,by decide⟩,⟨2,by decide⟩,⟨16,by decide⟩] | 2 => ![⟨18,by decide⟩,⟨15,by decide⟩,⟨18,by decide⟩] | 3 => ![⟨19,by decide⟩,⟨13,by decide⟩,⟨18,by decide⟩] | 4 => ![⟨3,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 5 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨20,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨21,by decide⟩] | _ => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨22,by decide⟩]

def ntree10LLLLLLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨23,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨24,by decide⟩,⟨24,by decide⟩] | 2 => ![⟨18,by decide⟩,⟨25,by decide⟩,⟨18,by decide⟩] | 3 => ![⟨19,by decide⟩,⟨26,by decide⟩,⟨27,by decide⟩] | 4 => ![⟨18,by decide⟩,⟨28,by decide⟩,⟨29,by decide⟩] | 5 => ![⟨30,by decide⟩,⟨30,by decide⟩,⟨9,by decide⟩] | 6 => ![⟨31,by decide⟩,⟨31,by decide⟩,⟨15,by decide⟩] | _ => ![⟨32,by decide⟩,⟨30,by decide⟩,⟨8,by decide⟩]

def ntree10LLLLLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLLLLLRL i else ntree10LLLLLLLRR (i - 8)

def ntree10LLLLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LLLLLLLL i else ntree10LLLLLLLR (i - 15)

def ntree10LLLLLLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨33,by decide⟩,⟨31,by decide⟩,⟨14,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨34,by decide⟩,⟨34,by decide⟩] | 2 => ![⟨31,by decide⟩,⟨31,by decide⟩,⟨35,by decide⟩] | 3 => ![⟨31,by decide⟩,⟨36,by decide⟩,⟨37,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨38,by decide⟩,⟨14,by decide⟩] | 5 => ![⟨33,by decide⟩,⟨39,by decide⟩,⟨40,by decide⟩] | 6 => ![⟨14,by decide⟩,⟨41,by decide⟩,⟨14,by decide⟩] | _ => ![⟨9,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩]

def ntree10LLLLLLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨42,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨43,by decide⟩,⟨8,by decide⟩] | 2 => ![⟨44,by decide⟩,⟨0,by decide⟩,⟨44,by decide⟩] | 3 => ![⟨45,by decide⟩,⟨1,by decide⟩,⟨44,by decide⟩] | 4 => ![⟨46,by decide⟩,⟨2,by decide⟩,⟨47,by decide⟩] | 5 => ![⟨48,by decide⟩,⟨9,by decide⟩,⟨48,by decide⟩] | 6 => ![⟨49,by decide⟩,⟨11,by decide⟩,⟨48,by decide⟩] | _ => ![⟨50,by decide⟩,⟨13,by decide⟩,⟨51,by decide⟩]

def ntree10LLLLLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLLLLRLL i else ntree10LLLLLLRLR (i - 8)

def ntree10LLLLLLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨52,by decide⟩,⟨3,by decide⟩,⟨52,by decide⟩] | 1 => ![⟨53,by decide⟩,⟨2,by decide⟩,⟨52,by decide⟩] | 2 => ![⟨54,by decide⟩,⟨15,by decide⟩,⟨54,by decide⟩] | 3 => ![⟨55,by decide⟩,⟨13,by decide⟩,⟨54,by decide⟩] | 4 => ![⟨47,by decide⟩,⟨3,by decide⟩,⟨47,by decide⟩] | 5 => ![⟨51,by decide⟩,⟨15,by decide⟩,⟨51,by decide⟩] | 6 => ![⟨51,by decide⟩,⟨56,by decide⟩,⟨51,by decide⟩] | _ => ![⟨50,by decide⟩,⟨57,by decide⟩,⟨58,by decide⟩]

def ntree10LLLLLLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨59,by decide⟩,⟨59,by decide⟩] | 1 => ![⟨13,by decide⟩,⟨60,by decide⟩,⟨61,by decide⟩] | 2 => ![⟨51,by decide⟩,⟨62,by decide⟩,⟨63,by decide⟩] | 3 => ![⟨50,by decide⟩,⟨64,by decide⟩,⟨65,by decide⟩] | 4 => ![⟨66,by decide⟩,⟨30,by decide⟩,⟨48,by decide⟩] | 5 => ![⟨67,by decide⟩,⟨31,by decide⟩,⟨51,by decide⟩] | 6 => ![⟨54,by decide⟩,⟨68,by decide⟩,⟨54,by decide⟩] | _ => ![⟨69,by decide⟩,⟨70,by decide⟩,⟨71,by decide⟩]

def ntree10LLLLLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLLLLRRL i else ntree10LLLLLLRRR (i - 8)

def ntree10LLLLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LLLLLLRL i else ntree10LLLLLLRR (i - 16)

def ntree10LLLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LLLLLLL i else ntree10LLLLLLR (i - 31)

def ntree10LLLLLRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨72,by decide⟩,⟨72,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨48,by decide⟩,⟨73,by decide⟩,⟨48,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨74,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨51,by decide⟩,⟨75,by decide⟩,⟨51,by decide⟩] | 5 => ![⟨76,by decide⟩,⟨77,by decide⟩,⟨76,by decide⟩] | _ => ![⟨78,by decide⟩,⟨79,by decide⟩,⟨76,by decide⟩]

def ntree10LLLLLRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3,by decide⟩,⟨3,by decide⟩,⟨80,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨81,by decide⟩] | 2 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨82,by decide⟩] | 3 => ![⟨51,by decide⟩,⟨24,by decide⟩,⟨83,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨25,by decide⟩,⟨81,by decide⟩] | 5 => ![⟨13,by decide⟩,⟨26,by decide⟩,⟨84,by decide⟩] | 6 => ![⟨51,by decide⟩,⟨28,by decide⟩,⟨83,by decide⟩] | _ => ![⟨50,by decide⟩,⟨26,by decide⟩,⟨85,by decide⟩]

def ntree10LLLLLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LLLLLRLLL i else ntree10LLLLLRLLR (i - 7)

def ntree10LLLLLRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨68,by decide⟩,⟨86,by decide⟩] | 1 => ![⟨31,by decide⟩,⟨70,by decide⟩,⟨87,by decide⟩] | 2 => ![⟨14,by decide⟩,⟨72,by decide⟩,⟨88,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨68,by decide⟩,⟨14,by decide⟩] | 4 => ![⟨51,by decide⟩,⟨68,by decide⟩,⟨51,by decide⟩] | 5 => ![⟨14,by decide⟩,⟨25,by decide⟩,⟨14,by decide⟩] | 6 => ![⟨76,by decide⟩,⟨89,by decide⟩,⟨76,by decide⟩] | _ => ![⟨90,by decide⟩,⟨90,by decide⟩,⟨0,by decide⟩]

def ntree10LLLLLRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨91,by decide⟩,⟨91,by decide⟩,⟨3,by decide⟩] | 1 => ![⟨92,by decide⟩,⟨90,by decide⟩,⟨4,by decide⟩] | 2 => ![⟨93,by decide⟩,⟨91,by decide⟩,⟨7,by decide⟩] | 3 => ![⟨94,by decide⟩,⟨95,by decide⟩,⟨8,by decide⟩] | 4 => ![⟨96,by decide⟩,⟨97,by decide⟩,⟨14,by decide⟩] | 5 => ![⟨98,by decide⟩,⟨98,by decide⟩,⟨9,by decide⟩] | 6 => ![⟨99,by decide⟩,⟨99,by decide⟩,⟨15,by decide⟩] | _ => ![⟨100,by decide⟩,⟨98,by decide⟩,⟨8,by decide⟩]

def ntree10LLLLLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLLLRLRL i else ntree10LLLLLRLRR (i - 8)

def ntree10LLLLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LLLLLRLL i else ntree10LLLLLRLR (i - 15)

def ntree10LLLLLRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨101,by decide⟩,⟨99,by decide⟩,⟨14,by decide⟩] | 1 => ![⟨102,by decide⟩,⟨91,by decide⟩,⟨16,by decide⟩] | 2 => ![⟨103,by decide⟩,⟨97,by decide⟩,⟨18,by decide⟩] | 3 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨91,by decide⟩,⟨91,by decide⟩,⟨104,by decide⟩] | 5 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨105,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨106,by decide⟩] | _ => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨107,by decide⟩]

def ntree10LLLLLRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨99,by decide⟩,⟨99,by decide⟩,⟨108,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨109,by decide⟩,⟨109,by decide⟩] | 2 => ![⟨110,by decide⟩,⟨111,by decide⟩,⟨112,by decide⟩] | 3 => ![⟨95,by decide⟩,⟨95,by decide⟩,⟨9,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨113,by decide⟩,⟨113,by decide⟩] | 5 => ![⟨97,by decide⟩,⟨114,by decide⟩,⟨115,by decide⟩] | 6 => ![⟨96,by decide⟩,⟨116,by decide⟩,⟨117,by decide⟩] | _ => ![⟨14,by decide⟩,⟨118,by decide⟩,⟨119,by decide⟩]

def ntree10LLLLLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLLLRRLL i else ntree10LLLLLRRLR (i - 8)

def ntree10LLLLLRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨96,by decide⟩,⟨120,by decide⟩,⟨121,by decide⟩] | 1 => ![⟨122,by decide⟩,⟨90,by decide⟩,⟨44,by decide⟩] | 2 => ![⟨123,by decide⟩,⟨91,by decide⟩,⟨47,by decide⟩] | 3 => ![⟨124,by decide⟩,⟨95,by decide⟩,⟨48,by decide⟩] | 4 => ![⟨125,by decide⟩,⟨97,by decide⟩,⟨51,by decide⟩] | 5 => ![⟨126,by decide⟩,⟨91,by decide⟩,⟨52,by decide⟩] | 6 => ![⟨127,by decide⟩,⟨97,by decide⟩,⟨54,by decide⟩] | _ => ![⟨128,by decide⟩,⟨98,by decide⟩,⟨48,by decide⟩]

def ntree10LLLLLRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨129,by decide⟩,⟨99,by decide⟩,⟨51,by decide⟩] | 1 => ![⟨129,by decide⟩,⟨130,by decide⟩,⟨131,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨132,by decide⟩,⟨132,by decide⟩] | 3 => ![⟨99,by decide⟩,⟨133,by decide⟩,⟨134,by decide⟩] | 4 => ![⟨127,by decide⟩,⟨135,by decide⟩,⟨136,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨137,by decide⟩,⟨137,by decide⟩] | 6 => ![⟨54,by decide⟩,⟨138,by decide⟩,⟨139,by decide⟩] | _ => ![⟨140,by decide⟩,⟨141,by decide⟩,⟨76,by decide⟩]

def ntree10LLLLLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLLLRRRL i else ntree10LLLLLRRRR (i - 8)

def ntree10LLLLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LLLLLRRL i else ntree10LLLLLRRR (i - 16)

def ntree10LLLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LLLLLRL i else ntree10LLLLLRR (i - 31)

def ntree10LLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10LLLLLL i else ntree10LLLLLR (i - 63)

def ntree10LLLLRLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3,by decide⟩,⟨3,by decide⟩,⟨142,by decide⟩] | 1 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨143,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨144,by decide⟩] | 3 => ![⟨51,by decide⟩,⟨109,by decide⟩,⟨145,by decide⟩] | 4 => ![⟨99,by decide⟩,⟨111,by decide⟩,⟨146,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨25,by decide⟩,⟨147,by decide⟩] | _ => ![⟨51,by decide⟩,⟨25,by decide⟩,⟨51,by decide⟩]

def ntree10LLLLRLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨97,by decide⟩,⟨135,by decide⟩,⟨148,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨68,by decide⟩,⟨144,by decide⟩] | 2 => ![⟨14,by decide⟩,⟨137,by decide⟩,⟨149,by decide⟩] | 3 => ![⟨96,by decide⟩,⟨135,by decide⟩,⟨150,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨138,by decide⟩,⟨149,by decide⟩] | 5 => ![⟨151,by decide⟩,⟨151,by decide⟩,⟨152,by decide⟩] | 6 => ![⟨153,by decide⟩,⟨151,by decide⟩,⟨154,by decide⟩] | _ => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨108,by decide⟩]

def ntree10LLLLRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LLLLRLLLL i else ntree10LLLLRLLLR (i - 7)

def ntree10LLLLRLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨35,by decide⟩] | 1 => ![⟨151,by decide⟩,⟨151,by decide⟩,⟨155,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨156,by decide⟩,⟨108,by decide⟩] | 3 => ![⟨13,by decide⟩,⟨157,by decide⟩,⟨109,by decide⟩] | 4 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨108,by decide⟩] | 5 => ![⟨18,by decide⟩,⟨146,by decide⟩,⟨112,by decide⟩] | 6 => ![⟨97,by decide⟩,⟨158,by decide⟩,⟨34,by decide⟩] | _ => ![⟨15,by decide⟩,⟨159,by decide⟩,⟨35,by decide⟩]

def ntree10LLLLRLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨97,by decide⟩,⟨158,by decide⟩,⟨37,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨160,by decide⟩,⟨40,by decide⟩] | 2 => ![⟨96,by decide⟩,⟨161,by decide⟩,⟨40,by decide⟩] | 3 => ![⟨9,by decide⟩,⟨162,by decide⟩,⟨9,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨159,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨14,by decide⟩,⟨163,by decide⟩,⟨14,by decide⟩] | 6 => ![⟨164,by decide⟩,⟨151,by decide⟩,⟨165,by decide⟩] | _ => ![⟨51,by decide⟩,⟨166,by decide⟩,⟨131,by decide⟩]

def ntree10LLLLRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLLRLLRL i else ntree10LLLLRLLRR (i - 8)

def ntree10LLLLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LLLLRLLL i else ntree10LLLLRLLR (i - 15)

def ntree10LLLLRLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨50,by decide⟩,⟨167,by decide⟩,⟨131,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨168,by decide⟩,⟨108,by decide⟩] | 2 => ![⟨13,by decide⟩,⟨169,by decide⟩,⟨132,by decide⟩] | 3 => ![⟨13,by decide⟩,⟨169,by decide⟩,⟨134,by decide⟩] | 4 => ![⟨54,by decide⟩,⟨87,by decide⟩,⟨71,by decide⟩] | 5 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨35,by decide⟩] | 6 => ![⟨97,by decide⟩,⟨170,by decide⟩,⟨72,by decide⟩] | _ => ![⟨15,by decide⟩,⟨171,by decide⟩,⟨35,by decide⟩]

def ntree10LLLLRLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨51,by decide⟩,⟨172,by decide⟩,⟨51,by decide⟩] | 1 => ![⟨9,by decide⟩,⟨173,by decide⟩,⟨9,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨168,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨174,by decide⟩,⟨175,by decide⟩,⟨176,by decide⟩] | 4 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨86,by decide⟩] | 5 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨147,by decide⟩] | 6 => ![⟨51,by decide⟩,⟨156,by decide⟩,⟨51,by decide⟩] | _ => ![⟨50,by decide⟩,⟨157,by decide⟩,⟨145,by decide⟩]

def ntree10LLLLRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLLRLRLL i else ntree10LLLLRLRLR (i - 8)

def ntree10LLLLRLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨146,by decide⟩,⟨146,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨87,by decide⟩,⟨87,by decide⟩] | 2 => ![⟨96,by decide⟩,⟨170,by decide⟩,⟨88,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨171,by decide⟩,⟨14,by decide⟩] | 4 => ![⟨177,by decide⟩,⟨177,by decide⟩,⟨3,by decide⟩] | 5 => ![⟨178,by decide⟩,⟨177,by decide⟩,⟨7,by decide⟩] | 6 => ![⟨179,by decide⟩,⟨180,by decide⟩,⟨14,by decide⟩] | _ => ![⟨3,by decide⟩,⟨181,by decide⟩,⟨181,by decide⟩]

def ntree10LLLLRLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨14,by decide⟩,⟨182,by decide⟩,⟨183,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨184,by decide⟩,⟨184,by decide⟩] | 2 => ![⟨180,by decide⟩,⟨180,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨15,by decide⟩,⟨185,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨186,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 5 => ![⟨187,by decide⟩,⟨187,by decide⟩,⟨3,by decide⟩] | 6 => ![⟨188,by decide⟩,⟨3,by decide⟩,⟨188,by decide⟩] | _ => ![⟨189,by decide⟩,⟨187,by decide⟩,⟨188,by decide⟩]

def ntree10LLLLRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLLRLRRL i else ntree10LLLLRLRRR (i - 8)

def ntree10LLLLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LLLLRLRL i else ntree10LLLLRLRR (i - 16)

def ntree10LLLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LLLLRLL i else ntree10LLLLRLR (i - 31)

def ntree10LLLLRRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨190,by decide⟩,⟨15,by decide⟩,⟨191,by decide⟩] | 1 => ![⟨192,by decide⟩,⟨193,by decide⟩,⟨191,by decide⟩] | 2 => ![⟨194,by decide⟩,⟨194,by decide⟩,⟨195,by decide⟩] | 3 => ![⟨186,by decide⟩,⟨196,by decide⟩,⟨196,by decide⟩] | 4 => ![⟨188,by decide⟩,⟨3,by decide⟩,⟨188,by decide⟩] | 5 => ![⟨190,by decide⟩,⟨197,by decide⟩,⟨198,by decide⟩] | _ => ![⟨191,by decide⟩,⟨15,by decide⟩,⟨191,by decide⟩]

def ntree10LLLLRRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨199,by decide⟩,⟨200,by decide⟩,⟨200,by decide⟩] | 1 => ![⟨201,by decide⟩,⟨201,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨202,by decide⟩,⟨15,by decide⟩,⟨202,by decide⟩] | 3 => ![⟨203,by decide⟩,⟨204,by decide⟩,⟨205,by decide⟩] | 4 => ![⟨206,by decide⟩,⟨84,by decide⟩,⟨84,by decide⟩] | 5 => ![⟨207,by decide⟩,⟨208,by decide⟩,⟨208,by decide⟩] | 6 => ![⟨209,by decide⟩,⟨209,by decide⟩,⟨208,by decide⟩] | _ => ![⟨210,by decide⟩,⟨201,by decide⟩,⟨211,by decide⟩]

def ntree10LLLLRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LLLLRRLLL i else ntree10LLLLRRLLR (i - 7)

def ntree10LLLLRRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨212,by decide⟩,⟨208,by decide⟩,⟨212,by decide⟩] | 1 => ![⟨213,by decide⟩,⟨209,by decide⟩,⟨212,by decide⟩] | 2 => ![⟨214,by decide⟩,⟨201,by decide⟩,⟨14,by decide⟩] | 3 => ![⟨215,by decide⟩,⟨195,by decide⟩,⟨215,by decide⟩] | 4 => ![⟨207,by decide⟩,⟨216,by decide⟩,⟨216,by decide⟩] | 5 => ![⟨208,by decide⟩,⟨208,by decide⟩,⟨208,by decide⟩] | 6 => ![⟨212,by decide⟩,⟨217,by decide⟩,⟨212,by decide⟩] | _ => ![⟨214,by decide⟩,⟨218,by decide⟩,⟨14,by decide⟩]

def ntree10LLLLRRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨219,by decide⟩,⟨177,by decide⟩,⟨47,by decide⟩] | 1 => ![⟨220,by decide⟩,⟨180,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨221,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 3 => ![⟨3,by decide⟩,⟨222,by decide⟩,⟨3,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨223,by decide⟩] | 5 => ![⟨224,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨225,by decide⟩,⟨15,by decide⟩] | _ => ![⟨15,by decide⟩,⟨226,by decide⟩,⟨227,by decide⟩]

def ntree10LLLLRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLLRRLRL i else ntree10LLLLRRLRR (i - 8)

def ntree10LLLLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LLLLRRLL i else ntree10LLLLRRLR (i - 15)

def ntree10LLLLRRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨228,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨229,by decide⟩,⟨187,by decide⟩,⟨47,by decide⟩] | 2 => ![⟨230,by decide⟩,⟨187,by decide⟩,⟨231,by decide⟩] | 3 => ![⟨232,by decide⟩,⟨193,by decide⟩,⟨51,by decide⟩] | 4 => ![⟨233,by decide⟩,⟨194,by decide⟩,⟨234,by decide⟩] | 5 => ![⟨235,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 6 => ![⟨231,by decide⟩,⟨222,by decide⟩,⟨231,by decide⟩] | _ => ![⟨236,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩]

def ntree10LLLLRRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨237,by decide⟩,⟨225,by decide⟩,⟨238,by decide⟩] | 1 => ![⟨239,by decide⟩,⟨240,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨241,by decide⟩,⟨242,by decide⟩,⟨243,by decide⟩] | 3 => ![⟨244,by decide⟩,⟨208,by decide⟩,⟨244,by decide⟩] | 4 => ![⟨245,by decide⟩,⟨209,by decide⟩,⟨244,by decide⟩] | 5 => ![⟨239,by decide⟩,⟨201,by decide⟩,⟨51,by decide⟩] | 6 => ![⟨246,by decide⟩,⟨208,by decide⟩,⟨208,by decide⟩] | _ => ![⟨247,by decide⟩,⟨201,by decide⟩,⟨248,by decide⟩]

def ntree10LLLLRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLLRRRLL i else ntree10LLLLRRRLR (i - 8)

def ntree10LLLLRRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨234,by decide⟩,⟨195,by decide⟩,⟨234,by decide⟩] | 1 => ![⟨249,by decide⟩,⟨250,by decide⟩,⟨250,by decide⟩] | 2 => ![⟨251,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨248,by decide⟩,⟨225,by decide⟩,⟨248,by decide⟩] | 4 => ![⟨252,by decide⟩,⟨253,by decide⟩,⟨254,by decide⟩] | 5 => ![⟨3,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 6 => ![⟨7,by decide⟩,⟨222,by decide⟩,⟨7,by decide⟩] | _ => ![⟨14,by decide⟩,⟨225,by decide⟩,⟨14,by decide⟩]

def ntree10LLLLRRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨51,by decide⟩,⟨255,by decide⟩,⟨51,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨228,by decide⟩,⟨14,by decide⟩] | 2 => ![⟨256,by decide⟩,⟨257,by decide⟩,⟨47,by decide⟩] | 3 => ![⟨258,by decide⟩,⟨257,by decide⟩,⟨188,by decide⟩] | 4 => ![⟨259,by decide⟩,⟨260,by decide⟩,⟨261,by decide⟩] | 5 => ![⟨261,by decide⟩,⟨262,by decide⟩,⟨261,by decide⟩] | 6 => ![⟨191,by decide⟩,⟨15,by decide⟩,⟨263,by decide⟩] | _ => ![⟨264,by decide⟩,⟨265,by decide⟩,⟨51,by decide⟩]

def ntree10LLLLRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLLRRRRL i else ntree10LLLLRRRRR (i - 8)

def ntree10LLLLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LLLLRRRL i else ntree10LLLLRRRR (i - 16)

def ntree10LLLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LLLLRRL i else ntree10LLLLRRR (i - 31)

def ntree10LLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10LLLLRL i else ntree10LLLLRR (i - 63)

def ntree10LLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 126 then ntree10LLLLL i else ntree10LLLLR (i - 126)

def ntree10LLLRLLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨266,by decide⟩,⟨265,by decide⟩,⟨202,by decide⟩] | 1 => ![⟨202,by decide⟩,⟨84,by decide⟩,⟨205,by decide⟩] | 2 => ![⟨51,by decide⟩,⟨84,by decide⟩,⟨85,by decide⟩] | 3 => ![⟨267,by decide⟩,⟨268,by decide⟩,⟨244,by decide⟩] | 4 => ![⟨269,by decide⟩,⟨268,by decide⟩,⟨212,by decide⟩] | 5 => ![⟨270,by decide⟩,⟨271,by decide⟩,⟨270,by decide⟩] | _ => ![⟨208,by decide⟩,⟨250,by decide⟩,⟨250,by decide⟩]

def ntree10LLLRLLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨272,by decide⟩,⟨265,by decide⟩,⟨14,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨273,by decide⟩,⟨274,by decide⟩] | 3 => ![⟨99,by decide⟩,⟨275,by decide⟩,⟨274,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨276,by decide⟩,⟨277,by decide⟩] | 5 => ![⟨278,by decide⟩,⟨91,by decide⟩,⟨188,by decide⟩] | 6 => ![⟨279,by decide⟩,⟨97,by decide⟩,⟨191,by decide⟩] | _ => ![⟨280,by decide⟩,⟨281,by decide⟩,⟨191,by decide⟩]

def ntree10LLLRLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LLLRLLLLL i else ntree10LLLRLLLLR (i - 7)

def ntree10LLLRLLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨282,by decide⟩,⟨282,by decide⟩,⟨195,by decide⟩] | 1 => ![⟨278,by decide⟩,⟨91,by decide⟩,⟨283,by decide⟩] | 2 => ![⟨279,by decide⟩,⟨97,by decide⟩,⟨284,by decide⟩] | 3 => ![⟨285,by decide⟩,⟨99,by decide⟩,⟨286,by decide⟩] | 4 => ![⟨287,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨281,by decide⟩,⟨281,by decide⟩,⟨288,by decide⟩] | 6 => ![⟨289,by decide⟩,⟨289,by decide⟩,⟨208,by decide⟩] | _ => ![⟨290,by decide⟩,⟨208,by decide⟩,⟨208,by decide⟩]

def ntree10LLLRLLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨291,by decide⟩,⟨97,by decide⟩,⟨211,by decide⟩] | 1 => ![⟨292,by decide⟩,⟨289,by decide⟩,⟨212,by decide⟩] | 2 => ![⟨293,by decide⟩,⟨294,by decide⟩,⟨212,by decide⟩] | 3 => ![⟨295,by decide⟩,⟨282,by decide⟩,⟨215,by decide⟩] | 4 => ![⟨289,by decide⟩,⟨289,by decide⟩,⟨296,by decide⟩] | 5 => ![⟨292,by decide⟩,⟨297,by decide⟩,⟨298,by decide⟩] | 6 => ![⟨299,by decide⟩,⟨299,by decide⟩,⟨15,by decide⟩] | _ => ![⟨300,by decide⟩,⟨301,by decide⟩,⟨274,by decide⟩]

def ntree10LLLRLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLRLLLRL i else ntree10LLLRLLLRR (i - 8)

def ntree10LLLRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LLLRLLLL i else ntree10LLLRLLLR (i - 15)

def ntree10LLLRLLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨302,by decide⟩,⟨303,by decide⟩,⟨14,by decide⟩] | 1 => ![⟨304,by decide⟩,⟨305,by decide⟩,⟨277,by decide⟩] | 2 => ![⟨3,by decide⟩,⟨306,by decide⟩,⟨306,by decide⟩] | 3 => ![⟨91,by decide⟩,⟨307,by decide⟩,⟨306,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨308,by decide⟩,⟨308,by decide⟩] | 5 => ![⟨97,by decide⟩,⟨309,by decide⟩,⟨308,by decide⟩] | 6 => ![⟨99,by decide⟩,⟨310,by decide⟩,⟨308,by decide⟩] | _ => ![⟨51,by decide⟩,⟨308,by decide⟩,⟨311,by decide⟩]

def ntree10LLLRLLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨312,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 1 => ![⟨313,by decide⟩,⟨91,by decide⟩,⟨231,by decide⟩] | 2 => ![⟨314,by decide⟩,⟨281,by decide⟩,⟨51,by decide⟩] | 3 => ![⟨315,by decide⟩,⟨282,by decide⟩,⟨234,by decide⟩] | 4 => ![⟨312,by decide⟩,⟨306,by decide⟩,⟨306,by decide⟩] | 5 => ![⟨313,by decide⟩,⟨307,by decide⟩,⟨316,by decide⟩] | 6 => ![⟨317,by decide⟩,⟨308,by decide⟩,⟨308,by decide⟩] | _ => ![⟨318,by decide⟩,⟨309,by decide⟩,⟨319,by decide⟩]

def ntree10LLLRLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLRLLRLL i else ntree10LLLRLLRLR (i - 8)

def ntree10LLLRLLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨320,by decide⟩,⟨310,by decide⟩,⟨321,by decide⟩] | 1 => ![⟨314,by decide⟩,⟨322,by decide⟩,⟨311,by decide⟩] | 2 => ![⟨323,by decide⟩,⟨289,by decide⟩,⟨244,by decide⟩] | 3 => ![⟨324,by decide⟩,⟨208,by decide⟩,⟨208,by decide⟩] | 4 => ![⟨318,by decide⟩,⟨97,by decide⟩,⟨248,by decide⟩] | 5 => ![⟨325,by decide⟩,⟨294,by decide⟩,⟨244,by decide⟩] | 6 => ![⟨324,by decide⟩,⟨326,by decide⟩,⟨326,by decide⟩] | _ => ![⟨327,by decide⟩,⟨328,by decide⟩,⟨51,by decide⟩]

def ntree10LLLRLLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨3,by decide⟩,⟨3,by decide⟩,⟨329,by decide⟩] | 1 => ![⟨91,by decide⟩,⟨91,by decide⟩,⟨329,by decide⟩] | 2 => ![⟨7,by decide⟩,⟨306,by decide⟩,⟨330,by decide⟩] | 3 => ![⟨93,by decide⟩,⟨307,by decide⟩,⟨330,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨308,by decide⟩,⟨331,by decide⟩] | 5 => ![⟨96,by decide⟩,⟨309,by decide⟩,⟨331,by decide⟩] | 6 => ![⟨51,by decide⟩,⟨332,by decide⟩,⟨333,by decide⟩] | _ => ![⟨129,by decide⟩,⟨334,by decide⟩,⟨333,by decide⟩]

def ntree10LLLRLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLRLLRRL i else ntree10LLLRLLRRR (i - 8)

def ntree10LLLRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LLLRLLRL i else ntree10LLLRLLRR (i - 16)

def ntree10LLLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LLLRLLL i else ntree10LLLRLLR (i - 31)

def ntree10LLLRLRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨101,by decide⟩,⟨310,by decide⟩,⟨331,by decide⟩] | 1 => ![⟨76,by decide⟩,⟨335,by decide⟩,⟨336,by decide⟩] | 2 => ![⟨337,by decide⟩,⟨338,by decide⟩,⟨261,by decide⟩] | 3 => ![⟨188,by decide⟩,⟨306,by decide⟩,⟨339,by decide⟩] | 4 => ![⟨191,by decide⟩,⟨308,by decide⟩,⟨340,by decide⟩] | 5 => ![⟨285,by decide⟩,⟨99,by decide⟩,⟨202,by decide⟩] | _ => ![⟨202,by decide⟩,⟨308,by decide⟩,⟨341,by decide⟩]

def ntree10LLLRLRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨342,by decide⟩,⟨343,by decide⟩,⟨51,by decide⟩] | 1 => ![⟨344,by decide⟩,⟨345,by decide⟩,⟨270,by decide⟩] | 2 => ![⟨208,by decide⟩,⟨208,by decide⟩,⟨346,by decide⟩] | 3 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨347,by decide⟩] | 4 => ![⟨212,by decide⟩,⟨326,by decide⟩,⟨348,by decide⟩] | 5 => ![⟨327,by decide⟩,⟨299,by decide⟩,⟨51,by decide⟩] | 6 => ![⟨302,by decide⟩,⟨299,by decide⟩,⟨14,by decide⟩] | _ => ![⟨349,by decide⟩,⟨350,by decide⟩,⟨76,by decide⟩]

def ntree10LLLRLRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LLLRLRLLL i else ntree10LLLRLRLLR (i - 7)

def ntree10LLLRLRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨97,by decide⟩,⟨351,by decide⟩,⟨352,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨353,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨96,by decide⟩,⟨354,by decide⟩,⟨355,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨356,by decide⟩,⟨14,by decide⟩] | 4 => ![⟨180,by decide⟩,⟨357,by decide⟩,⟨274,by decide⟩] | 5 => ![⟨179,by decide⟩,⟨358,by decide⟩,⟨277,by decide⟩] | 6 => ![⟨359,by decide⟩,⟨97,by decide⟩,⟨360,by decide⟩] | _ => ![⟨361,by decide⟩,⟨201,by decide⟩,⟨360,by decide⟩]

def ntree10LLLRLRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨362,by decide⟩,⟨362,by decide⟩,⟨363,by decide⟩] | 1 => ![⟨364,by decide⟩,⟨97,by decide⟩,⟨202,by decide⟩] | 2 => ![⟨203,by decide⟩,⟨201,by decide⟩,⟨202,by decide⟩] | 3 => ![⟨206,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨359,by decide⟩,⟨365,by decide⟩,⟨366,by decide⟩] | 5 => ![⟨360,by decide⟩,⟨367,by decide⟩,⟨360,by decide⟩] | 6 => ![⟨364,by decide⟩,⟨97,by decide⟩,⟨286,by decide⟩] | _ => ![⟨202,by decide⟩,⟨15,by decide⟩,⟨202,by decide⟩]

def ntree10LLLRLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLRLRLRL i else ntree10LLLRLRLRR (i - 8)

def ntree10LLLRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LLLRLRLL i else ntree10LLLRLRLR (i - 15)

def ntree10LLLRLRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨368,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨199,by decide⟩,⟨369,by decide⟩,⟨108,by decide⟩] | 3 => ![⟨201,by decide⟩,⟨370,by decide⟩,⟨109,by decide⟩] | 4 => ![⟨201,by decide⟩,⟨201,by decide⟩,⟨108,by decide⟩] | 5 => ![⟨202,by decide⟩,⟨15,by decide⟩,⟨286,by decide⟩] | 6 => ![⟨206,by decide⟩,⟨371,by decide⟩,⟨288,by decide⟩] | _ => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨288,by decide⟩]

def ntree10LLLRLRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨372,by decide⟩,⟨362,by decide⟩,⟨373,by decide⟩] | 1 => ![⟨359,by decide⟩,⟨158,by decide⟩,⟨374,by decide⟩] | 2 => ![⟨360,by decide⟩,⟨159,by decide⟩,⟨360,by decide⟩] | 3 => ![⟨199,by decide⟩,⟨159,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨201,by decide⟩,⟨375,by decide⟩,⟨274,by decide⟩] | 5 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨376,by decide⟩] | 6 => ![⟨224,by decide⟩,⟨308,by decide⟩,⟨308,by decide⟩] | _ => ![⟨15,by decide⟩,⟨377,by decide⟩,⟨15,by decide⟩]

def ntree10LLLRLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLRLRRLL i else ntree10LLLRLRRLR (i - 8)

def ntree10LLLRLRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨180,by decide⟩,⟨378,by decide⟩,⟨308,by decide⟩] | 1 => ![⟨51,by decide⟩,⟨377,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨220,by decide⟩,⟨378,by decide⟩,⟨311,by decide⟩] | 3 => ![⟨379,by decide⟩,⟨362,by decide⟩,⟨380,by decide⟩] | 4 => ![⟨381,by decide⟩,⟨201,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨382,by decide⟩,⟨362,by decide⟩,⟨383,by decide⟩] | 6 => ![⟨251,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | _ => ![⟨384,by decide⟩,⟨97,by decide⟩,⟨385,by decide⟩]

def ntree10LLLRLRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨386,by decide⟩,⟨308,by decide⟩,⟨308,by decide⟩] | 1 => ![⟨387,by decide⟩,⟨309,by decide⟩,⟨321,by decide⟩] | 2 => ![⟨239,by decide⟩,⟨388,by decide⟩,⟨131,by decide⟩] | 3 => ![⟨201,by decide⟩,⟨389,by decide⟩,⟨308,by decide⟩] | 4 => ![⟨241,by decide⟩,⟨389,by decide⟩,⟨321,by decide⟩] | 5 => ![⟨390,by decide⟩,⟨97,by decide⟩,⟨391,by decide⟩] | 6 => ![⟨392,by decide⟩,⟨201,by decide⟩,⟨391,by decide⟩] | _ => ![⟨251,by decide⟩,⟨87,by decide⟩,⟨87,by decide⟩]

def ntree10LLLRLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLRLRRRL i else ntree10LLLRLRRRR (i - 8)

def ntree10LLLRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LLLRLRRL i else ntree10LLLRLRRR (i - 16)

def ntree10LLLRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LLLRLRL i else ntree10LLLRLRR (i - 31)

def ntree10LLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10LLLRLL i else ntree10LLLRLR (i - 63)

def ntree10LLLRRLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨384,by decide⟩,⟨97,by decide⟩,⟨393,by decide⟩] | 1 => ![⟨252,by decide⟩,⟨168,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨347,by decide⟩] | 3 => ![⟨394,by decide⟩,⟨395,by decide⟩,⟨396,by decide⟩] | 4 => ![⟨396,by decide⟩,⟨397,by decide⟩,⟨396,by decide⟩] | 5 => ![⟨398,by decide⟩,⟨395,by decide⟩,⟨399,by decide⟩] | _ => ![⟨399,by decide⟩,⟨397,by decide⟩,⟨399,by decide⟩]

def ntree10LLLRRLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨360,by decide⟩,⟨15,by decide⟩,⟨400,by decide⟩] | 1 => ![⟨401,by decide⟩,⟨395,by decide⟩,⟨402,by decide⟩] | 2 => ![⟨402,by decide⟩,⟨397,by decide⟩,⟨402,by decide⟩] | 3 => ![⟨360,by decide⟩,⟨87,by decide⟩,⟨403,by decide⟩] | 4 => ![⟨404,by decide⟩,⟨9,by decide⟩,⟨404,by decide⟩] | 5 => ![⟨405,by decide⟩,⟨11,by decide⟩,⟨404,by decide⟩] | 6 => ![⟨406,by decide⟩,⟨13,by decide⟩,⟨407,by decide⟩] | _ => ![⟨407,by decide⟩,⟨15,by decide⟩,⟨407,by decide⟩]

def ntree10LLLRRLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LLLRRLLLL i else ntree10LLLRRLLLR (i - 7)

def ntree10LLLRRLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨9,by decide⟩,⟨408,by decide⟩,⟨408,by decide⟩] | 1 => ![⟨13,by decide⟩,⟨409,by decide⟩,⟨410,by decide⟩] | 2 => ![⟨411,by decide⟩,⟨412,by decide⟩,⟨412,by decide⟩] | 3 => ![⟨413,by decide⟩,⟨413,by decide⟩,⟨412,by decide⟩] | 4 => ![⟨414,by decide⟩,⟨412,by decide⟩,⟨414,by decide⟩] | 5 => ![⟨415,by decide⟩,⟨413,by decide⟩,⟨414,by decide⟩] | 6 => ![⟨416,by decide⟩,⟨417,by decide⟩,⟨191,by decide⟩] | _ => ![⟨418,by decide⟩,⟨13,by decide⟩,⟨191,by decide⟩]

def ntree10LLLRRLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨419,by decide⟩,⟨419,by decide⟩,⟨195,by decide⟩] | 1 => ![⟨418,by decide⟩,⟨13,by decide⟩,⟨420,by decide⟩] | 2 => ![⟨411,by decide⟩,⟨421,by decide⟩,⟨421,by decide⟩] | 3 => ![⟨413,by decide⟩,⟨413,by decide⟩,⟨422,by decide⟩] | 4 => ![⟨412,by decide⟩,⟨412,by decide⟩,⟨412,by decide⟩] | 5 => ![⟨423,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | 6 => ![⟨424,by decide⟩,⟨424,by decide⟩,⟨9,by decide⟩] | _ => ![⟨425,by decide⟩,⟨201,by decide⟩,⟨15,by decide⟩]

def ntree10LLLRRLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLRRLLRL i else ntree10LLLRRLLRR (i - 8)

def ntree10LLLRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LLLRRLLL i else ntree10LLLRRLLR (i - 15)

def ntree10LLLRRLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨426,by decide⟩,⟨9,by decide⟩,⟨426,by decide⟩] | 1 => ![⟨427,by decide⟩,⟨424,by decide⟩,⟨426,by decide⟩] | 2 => ![⟨428,by decide⟩,⟨201,by decide⟩,⟨429,by decide⟩] | 3 => ![⟨430,by decide⟩,⟨195,by decide⟩,⟨430,by decide⟩] | 4 => ![⟨431,by decide⟩,⟨431,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨432,by decide⟩,⟨433,by decide⟩,⟨434,by decide⟩] | 6 => ![⟨435,by decide⟩,⟨160,by decide⟩,⟨160,by decide⟩] | _ => ![⟨423,by decide⟩,⟨436,by decide⟩,⟨436,by decide⟩]

def ntree10LLLRRLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨424,by decide⟩,⟨424,by decide⟩,⟨9,by decide⟩] | 1 => ![⟨425,by decide⟩,⟨437,by decide⟩,⟨438,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨439,by decide⟩,⟨440,by decide⟩] | 3 => ![⟨13,by decide⟩,⟨441,by decide⟩,⟨442,by decide⟩] | 4 => ![⟨54,by decide⟩,⟨439,by decide⟩,⟨443,by decide⟩] | 5 => ![⟨444,by decide⟩,⟨412,by decide⟩,⟨444,by decide⟩] | 6 => ![⟨445,by decide⟩,⟨413,by decide⟩,⟨444,by decide⟩] | _ => ![⟨446,by decide⟩,⟨412,by decide⟩,⟨412,by decide⟩]

def ntree10LLLRRLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLRRLRLL i else ntree10LLLRRLRLR (i - 8)

def ntree10LLLRRLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨447,by decide⟩,⟨413,by decide⟩,⟨448,by decide⟩] | 1 => ![⟨449,by decide⟩,⟨417,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨450,by decide⟩,⟨419,by decide⟩,⟨234,by decide⟩] | 3 => ![⟨451,by decide⟩,⟨15,by decide⟩,⟨451,by decide⟩] | 4 => ![⟨452,by decide⟩,⟨13,by decide⟩,⟨453,by decide⟩] | 5 => ![⟨454,by decide⟩,⟨439,by decide⟩,⟨455,by decide⟩] | 6 => ![⟨456,by decide⟩,⟨441,by decide⟩,⟨457,by decide⟩] | _ => ![⟨444,by decide⟩,⟨458,by decide⟩,⟨444,by decide⟩]

def ntree10LLLRRLRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨445,by decide⟩,⟨459,by decide⟩,⟨460,by decide⟩] | 1 => ![⟨461,by decide⟩,⟨424,by decide⟩,⟨48,by decide⟩] | 2 => ![⟨462,by decide⟩,⟨463,by decide⟩,⟨54,by decide⟩] | 3 => ![⟨461,by decide⟩,⟨464,by decide⟩,⟨48,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨465,by decide⟩] | 5 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨466,by decide⟩] | 6 => ![⟨407,by decide⟩,⟨439,by decide⟩,⟨467,by decide⟩] | _ => ![⟨406,by decide⟩,⟨441,by decide⟩,⟨468,by decide⟩]

def ntree10LLLRRLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLRRLRRL i else ntree10LLLRRLRRR (i - 8)

def ntree10LLLRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LLLRRLRL i else ntree10LLLRRLRR (i - 16)

def ntree10LLLRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LLLRRLL i else ntree10LLLRRLR (i - 31)

def ntree10LLLRRRLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨51,by decide⟩,⟨469,by decide⟩,⟨470,by decide⟩] | 1 => ![⟨50,by decide⟩,⟨471,by decide⟩,⟨472,by decide⟩] | 2 => ![⟨473,by decide⟩,⟨265,by decide⟩,⟨191,by decide⟩] | 3 => ![⟨474,by decide⟩,⟨475,by decide⟩,⟨261,by decide⟩] | 4 => ![⟨199,by decide⟩,⟨15,by decide⟩,⟨81,by decide⟩] | 5 => ![⟨191,by decide⟩,⟨439,by decide⟩,⟨476,by decide⟩] | _ => ![⟨264,by decide⟩,⟨477,by decide⟩,⟨83,by decide⟩]

def ntree10LLLRRRLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨265,by decide⟩,⟨265,by decide⟩,⟨81,by decide⟩] | 1 => ![⟨478,by decide⟩,⟨431,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨432,by decide⟩,⟨431,by decide⟩,⟨191,by decide⟩] | 3 => ![⟨435,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨199,by decide⟩,⟨68,by decide⟩,⟨479,by decide⟩] | 5 => ![⟨431,by decide⟩,⟨463,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | _ => ![⟨191,by decide⟩,⟨72,by decide⟩,⟨480,by decide⟩]

def ntree10LLLRRRLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LLLRRRLLL i else ntree10LLLRRRLLR (i - 7)

def ntree10LLLRRRLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨435,by decide⟩,⟨225,by decide⟩,⟨481,by decide⟩] | 1 => ![⟨191,by decide⟩,⟨68,by decide⟩,⟨191,by decide⟩] | 2 => ![⟨264,by decide⟩,⟨482,by decide⟩,⟨483,by decide⟩] | 3 => ![⟨478,by decide⟩,⟨463,by decide⟩,⟨51,by decide⟩] | 4 => ![⟨51,by decide⟩,⟨484,by decide⟩,⟨51,by decide⟩] | 5 => ![⟨265,by decide⟩,⟨265,by decide⟩,⟨485,by decide⟩] | 6 => ![⟨431,by decide⟩,⟨431,by decide⟩,⟨15,by decide⟩] | _ => ![⟨486,by decide⟩,⟨95,by decide⟩,⟨404,by decide⟩]

def ntree10LLLRRRLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨487,by decide⟩,⟨97,by decide⟩,⟨407,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨488,by decide⟩,⟨489,by decide⟩] | 2 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨490,by decide⟩] | 3 => ![⟨491,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | 4 => ![⟨492,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨9,by decide⟩,⟨9,by decide⟩,⟨493,by decide⟩] | 6 => ![⟨494,by decide⟩,⟨494,by decide⟩,⟨412,by decide⟩] | _ => ![⟨495,by decide⟩,⟨412,by decide⟩,⟨412,by decide⟩]

def ntree10LLLRRRLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLRRRLRL i else ntree10LLLRRRLRR (i - 8)

def ntree10LLLRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LLLRRRLL i else ntree10LLLRRRLR (i - 15)

def ntree10LLLRRRRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨496,by decide⟩,⟨494,by decide⟩,⟨414,by decide⟩] | 1 => ![⟨497,by decide⟩,⟨498,by decide⟩,⟨499,by decide⟩] | 2 => ![⟨500,by decide⟩,⟨501,by decide⟩,⟨501,by decide⟩] | 3 => ![⟨502,by decide⟩,⟨95,by decide⟩,⟨426,by decide⟩] | 4 => ![⟨503,by decide⟩,⟨97,by decide⟩,⟨429,by decide⟩] | 5 => ![⟨504,by decide⟩,⟨505,by decide⟩,⟨426,by decide⟩] | 6 => ![⟨506,by decide⟩,⟨282,by decide⟩,⟨430,by decide⟩] | _ => ![⟨507,by decide⟩,⟨508,by decide⟩,⟨509,by decide⟩]

def ntree10LLLRRRRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨510,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | 1 => ![⟨511,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨505,by decide⟩,⟨505,by decide⟩,⟨493,by decide⟩] | 3 => ![⟨512,by decide⟩,⟨513,by decide⟩,⟨288,by decide⟩] | 4 => ![⟨54,by decide⟩,⟨308,by decide⟩,⟨514,by decide⟩] | 5 => ![⟨9,by decide⟩,⟨515,by decide⟩,⟨515,by decide⟩] | 6 => ![⟨48,by decide⟩,⟨515,by decide⟩,⟨516,by decide⟩] | _ => ![⟨517,by decide⟩,⟨494,by decide⟩,⟨444,by decide⟩]

def ntree10LLLRRRRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLRRRRLL i else ntree10LLLRRRRLR (i - 8)

def ntree10LLLRRRRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨518,by decide⟩,⟨412,by decide⟩,⟨412,by decide⟩] | 1 => ![⟨519,by decide⟩,⟨494,by decide⟩,⟨448,by decide⟩] | 2 => ![⟨520,by decide⟩,⟨97,by decide⟩,⟨521,by decide⟩] | 3 => ![⟨518,by decide⟩,⟨522,by decide⟩,⟨522,by decide⟩] | 4 => ![⟨523,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | 5 => ![⟨524,by decide⟩,⟨505,by decide⟩,⟨48,by decide⟩] | 6 => ![⟨525,by decide⟩,⟨526,by decide⟩,⟨514,by decide⟩] | _ => ![⟨523,by decide⟩,⟨515,by decide⟩,⟨515,by decide⟩]

def ntree10LLLRRRRRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨524,by decide⟩,⟨527,by decide⟩,⟨516,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨528,by decide⟩] | 2 => ![⟨97,by decide⟩,⟨97,by decide⟩,⟨528,by decide⟩] | 3 => ![⟨407,by decide⟩,⟨308,by decide⟩,⟨529,by decide⟩] | 4 => ![⟨487,by decide⟩,⟨309,by decide⟩,⟨529,by decide⟩] | 5 => ![⟨492,by decide⟩,⟨308,by decide⟩,⟨308,by decide⟩] | 6 => ![⟨530,by decide⟩,⟨531,by decide⟩,⟨51,by decide⟩] | _ => ![⟨532,by decide⟩,⟨531,by decide⟩,⟨191,by decide⟩]

def ntree10LLLRRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLLRRRRRL i else ntree10LLLRRRRRR (i - 8)

def ntree10LLLRRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 16 then ntree10LLLRRRRL i else ntree10LLLRRRRR (i - 16)

def ntree10LLLRRR (i : Nat) : Fin 3 → Fin 3959 := if i < 31 then ntree10LLLRRRL i else ntree10LLLRRRR (i - 31)

def ntree10LLLRR (i : Nat) : Fin 3 → Fin 3959 := if i < 63 then ntree10LLLRRL i else ntree10LLLRRR (i - 63)

def ntree10LLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 126 then ntree10LLLRL i else ntree10LLLRR (i - 126)

def ntree10LLL (i : Nat) : Fin 3 → Fin 3959 := if i < 252 then ntree10LLLL i else ntree10LLLR (i - 252)

def ntree10LLRLLLLLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨497,by decide⟩,⟨15,by decide⟩,⟨144,by decide⟩] | 1 => ![⟨287,by decide⟩,⟨146,by decide⟩,⟨146,by decide⟩] | 2 => ![⟨533,by decide⟩,⟨15,by decide⟩,⟨191,by decide⟩] | 3 => ![⟨534,by decide⟩,⟨535,by decide⟩,⟨261,by decide⟩] | 4 => ![⟨279,by decide⟩,⟨135,by decide⟩,⟨536,by decide⟩] | 5 => ![⟨507,by decide⟩,⟨526,by decide⟩,⟨340,by decide⟩] | _ => ![⟨287,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩]

def ntree10LLRLLLLLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨537,by decide⟩,⟨308,by decide⟩,⟨308,by decide⟩] | 1 => ![⟨342,by decide⟩,⟨538,by decide⟩,⟨51,by decide⟩] | 2 => ![⟨539,by decide⟩,⟨526,by decide⟩,⟨311,by decide⟩] | 3 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨490,by decide⟩] | 4 => ![⟨9,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩] | 5 => ![⟨11,by decide⟩,⟨11,by decide⟩,⟨493,by decide⟩] | 6 => ![⟨13,by decide⟩,⟨13,by decide⟩,⟨288,by decide⟩] | _ => ![⟨540,by decide⟩,⟨494,by decide⟩,⟨541,by decide⟩]

def ntree10LLRLLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 7 then ntree10LLRLLLLLL i else ntree10LLRLLLLLR (i - 7)

def ntree10LLRLLLLRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨542,by decide⟩,⟨413,by decide⟩,⟨541,by decide⟩] | 1 => ![⟨543,by decide⟩,⟨543,by decide⟩,⟨544,by decide⟩] | 2 => ![⟨545,by decide⟩,⟨13,by decide⟩,⟨360,by decide⟩] | 3 => ![⟨412,by decide⟩,⟨501,by decide⟩,⟨501,by decide⟩] | 4 => ![⟨15,by decide⟩,⟨15,by decide⟩,⟨15,by decide⟩] | 5 => ![⟨546,by decide⟩,⟨95,by decide⟩,⟨547,by decide⟩] | 6 => ![⟨548,by decide⟩,⟨424,by decide⟩,⟨547,by decide⟩] | _ => ![⟨549,by decide⟩,⟨362,by decide⟩,⟨550,by decide⟩]

def ntree10LLRLLLLRR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨551,by decide⟩,⟨431,by decide⟩,⟨360,by decide⟩] | 1 => ![⟨431,by decide⟩,⟨433,by decide⟩,⟨160,by decide⟩] | 2 => ![⟨97,by decide⟩,⟨161,by decide⟩,⟨160,by decide⟩] | 3 => ![⟨201,by decide⟩,⟨552,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨97,by decide⟩,⟨553,by decide⟩,⟨554,by decide⟩] | 5 => ![⟨13,by decide⟩,⟨555,by decide⟩,⟨308,by decide⟩] | 6 => ![⟨151,by decide⟩,⟨556,by decide⟩,⟨557,by decide⟩] | _ => ![⟨127,by decide⟩,⟨553,by decide⟩,⟨558,by decide⟩]

def ntree10LLRLLLLR (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRLLLLRL i else ntree10LLRLLLLRR (i - 8)

def ntree10LLRLLLL (i : Nat) : Fin 3 → Fin 3959 := if i < 15 then ntree10LLRLLLLL i else ntree10LLRLLLLR (i - 15)

def ntree10LLRLLLRLL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨55,by decide⟩,⟨555,by decide⟩,⟨514,by decide⟩] | 1 => ![⟨9,by decide⟩,⟨559,by decide⟩,⟨9,by decide⟩] | 2 => ![⟨11,by decide⟩,⟨560,by decide⟩,⟨515,by decide⟩] | 3 => ![⟨48,by decide⟩,⟨559,by decide⟩,⟨48,by decide⟩] | 4 => ![⟨49,by decide⟩,⟨560,by decide⟩,⟨516,by decide⟩] | 5 => ![⟨50,by decide⟩,⟨555,by decide⟩,⟨311,by decide⟩] | 6 => ![⟨561,by decide⟩,⟨543,by decide⟩,⟨562,by decide⟩] | _ => ![⟨520,by decide⟩,⟨97,by decide⟩,⟨451,by decide⟩]

def ntree10LLRLLLRLR (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨452,by decide⟩,⟨13,by decide⟩,⟨451,by decide⟩] | 1 => ![⟨563,by decide⟩,⟨151,by decide⟩,⟨564,by decide⟩] | 2 => ![⟨412,by decide⟩,⟨565,by decide⟩,⟨412,by decide⟩] | 3 => ![⟨413,by decide⟩,⟨566,by decide⟩,⟨522,by decide⟩] | 4 => ![⟨51,by decide⟩,⟨567,by decide⟩,⟨51,by decide⟩] | 5 => ![⟨462,by decide⟩,⟨431,by decide⟩,⟨54,by decide⟩] | 6 => ![⟨431,by decide⟩,⟨568,by decide⟩,⟨308,by decide⟩] | _ => ![⟨424,by decide⟩,⟨569,by decide⟩,⟨515,by decide⟩]

def ntree10LLRLLLRL (i : Nat) : Fin 3 → Fin 3959 := if i < 8 then ntree10LLRLLLRLL i else ntree10LLRLLLRLR (i - 8)

def ntree10LLRLLLRRL (i : Nat) : Fin 3 → Fin 3959 := match i with | 0 => ![⟨15,by decide⟩,⟨567,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨570,by decide⟩,⟨571,by decide⟩,⟨396,by decide⟩] | 2 => ![⟨395,by decide⟩,⟨395,by decide⟩,⟨397,by decide⟩] | 3 => ![⟨571,by decide⟩,⟨571,by decide⟩,⟨397,by decide⟩] | 4 => ![⟨265,by decide⟩,⟨572,by decide⟩,⟨146,by decide⟩] | 5 => ![⟨573,by decide⟩,⟨574,by decide⟩,⟨396,by decide⟩] | 6 => ![⟨574,by decide⟩,⟨574,by decide⟩,⟨397,by decide⟩] | _ => ![⟨265,by decide⟩,⟨575,by decide⟩,⟨15,by decide⟩]

end Paper2.Certificates.Q6.Coverage
