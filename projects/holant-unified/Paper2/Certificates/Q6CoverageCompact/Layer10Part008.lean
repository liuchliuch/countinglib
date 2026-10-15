import Paper2.Certificates.Q6CoverageCompact.Layer10Part007

namespace Paper2.Certificates.Q6.Coverage

def stree10LLRLLLRRL (i : Nat) : State := match i with | 0 => state10_539 | 1 => state10_540 | 2 => state10_541 | 3 => state10_542 | 4 => state10_543 | 5 => state10_544 | 6 => state10_545 | _ => state10_546

def stree10LLRLLLRRR (i : Nat) : State := match i with | 0 => state10_547 | 1 => state10_548 | 2 => state10_549 | 3 => state10_550 | 4 => state10_551 | 5 => state10_552 | 6 => state10_553 | _ => state10_554

def stree10LLRLLLRR (i : Nat) : State := if i < 8 then stree10LLRLLLRRL i else stree10LLRLLLRRR (i - 8)

def stree10LLRLLLR (i : Nat) : State := if i < 15 then stree10LLRLLLRL i else stree10LLRLLLRR (i - 15)

def stree10LLRLLL (i : Nat) : State := if i < 30 then stree10LLRLLLL i else stree10LLRLLLR (i - 30)

def stree10LLRLLRLLL (i : Nat) : State := match i with | 0 => state10_555 | 1 => state10_556 | 2 => state10_557 | 3 => state10_558 | 4 => state10_559 | 5 => state10_560 | _ => state10_561

def stree10LLRLLRLLR (i : Nat) : State := match i with | 0 => state10_562 | 1 => state10_563 | 2 => state10_564 | 3 => state10_565 | 4 => state10_566 | 5 => state10_567 | 6 => state10_568 | _ => state10_569

def stree10LLRLLRLL (i : Nat) : State := if i < 7 then stree10LLRLLRLLL i else stree10LLRLLRLLR (i - 7)

def stree10LLRLLRLRL (i : Nat) : State := match i with | 0 => state10_570 | 1 => state10_571 | 2 => state10_572 | 3 => state10_573 | 4 => state10_574 | 5 => state10_575 | 6 => state10_576 | _ => state10_577

def stree10LLRLLRLRR (i : Nat) : State := match i with | 0 => state10_578 | 1 => state10_579 | 2 => state10_580 | 3 => state10_581 | 4 => state10_582 | 5 => state10_583 | 6 => state10_584 | _ => state10_585

def stree10LLRLLRLR (i : Nat) : State := if i < 8 then stree10LLRLLRLRL i else stree10LLRLLRLRR (i - 8)

def stree10LLRLLRL (i : Nat) : State := if i < 15 then stree10LLRLLRLL i else stree10LLRLLRLR (i - 15)

def stree10LLRLLRRLL (i : Nat) : State := match i with | 0 => state10_586 | 1 => state10_587 | 2 => state10_588 | 3 => state10_589 | 4 => state10_590 | 5 => state10_591 | _ => state10_592

def stree10LLRLLRRLR (i : Nat) : State := match i with | 0 => state10_593 | 1 => state10_594 | 2 => state10_595 | 3 => state10_596 | 4 => state10_597 | 5 => state10_598 | 6 => state10_599 | _ => state10_600

def stree10LLRLLRRL (i : Nat) : State := if i < 7 then stree10LLRLLRRLL i else stree10LLRLLRRLR (i - 7)

def stree10LLRLLRRRL (i : Nat) : State := match i with | 0 => state10_601 | 1 => state10_602 | 2 => state10_603 | 3 => state10_604 | 4 => state10_605 | 5 => state10_606 | 6 => state10_607 | _ => state10_608

def stree10LLRLLRRRR (i : Nat) : State := match i with | 0 => state10_609 | 1 => state10_610 | 2 => state10_611 | 3 => state10_612 | 4 => state10_613 | 5 => state10_614 | 6 => state10_615 | _ => state10_616

def stree10LLRLLRRR (i : Nat) : State := if i < 8 then stree10LLRLLRRRL i else stree10LLRLLRRRR (i - 8)

def stree10LLRLLRR (i : Nat) : State := if i < 15 then stree10LLRLLRRL i else stree10LLRLLRRR (i - 15)

def stree10LLRLLR (i : Nat) : State := if i < 31 then stree10LLRLLRL i else stree10LLRLLRR (i - 31)

def stree10LLRLL (i : Nat) : State := if i < 61 then stree10LLRLLL i else stree10LLRLLR (i - 61)

def stree10LLRLRLLLL (i : Nat) : State := match i with | 0 => state10_617 | 1 => state10_618 | 2 => state10_619 | 3 => state10_620 | 4 => state10_621 | 5 => state10_622 | _ => state10_623

def stree10LLRLRLLLR (i : Nat) : State := match i with | 0 => state10_624 | 1 => state10_625 | 2 => state10_626 | 3 => state10_627 | 4 => state10_628 | 5 => state10_629 | 6 => state10_630 | _ => state10_631

def stree10LLRLRLLL (i : Nat) : State := if i < 7 then stree10LLRLRLLLL i else stree10LLRLRLLLR (i - 7)

def stree10LLRLRLLRL (i : Nat) : State := match i with | 0 => state10_632 | 1 => state10_633 | 2 => state10_634 | 3 => state10_635 | 4 => state10_636 | 5 => state10_637 | 6 => state10_638 | _ => state10_639

def stree10LLRLRLLRR (i : Nat) : State := match i with | 0 => state10_640 | 1 => state10_641 | 2 => state10_642 | 3 => state10_643 | 4 => state10_644 | 5 => state10_645 | 6 => state10_646 | _ => state10_647

def stree10LLRLRLLR (i : Nat) : State := if i < 8 then stree10LLRLRLLRL i else stree10LLRLRLLRR (i - 8)

def stree10LLRLRLL (i : Nat) : State := if i < 15 then stree10LLRLRLLL i else stree10LLRLRLLR (i - 15)

def stree10LLRLRLRLL (i : Nat) : State := match i with | 0 => state10_648 | 1 => state10_649 | 2 => state10_650 | 3 => state10_651 | 4 => state10_652 | 5 => state10_653 | _ => state10_654

def stree10LLRLRLRLR (i : Nat) : State := match i with | 0 => state10_655 | 1 => state10_656 | 2 => state10_657 | 3 => state10_658 | 4 => state10_659 | 5 => state10_660 | 6 => state10_661 | _ => state10_662

def stree10LLRLRLRL (i : Nat) : State := if i < 7 then stree10LLRLRLRLL i else stree10LLRLRLRLR (i - 7)

def stree10LLRLRLRRL (i : Nat) : State := match i with | 0 => state10_663 | 1 => state10_664 | 2 => state10_665 | 3 => state10_666 | 4 => state10_667 | 5 => state10_668 | 6 => state10_669 | _ => state10_670

def stree10LLRLRLRRR (i : Nat) : State := match i with | 0 => state10_671 | 1 => state10_672 | 2 => state10_673 | 3 => state10_674 | 4 => state10_675 | 5 => state10_676 | 6 => state10_677 | _ => state10_678

def stree10LLRLRLRR (i : Nat) : State := if i < 8 then stree10LLRLRLRRL i else stree10LLRLRLRRR (i - 8)

def stree10LLRLRLR (i : Nat) : State := if i < 15 then stree10LLRLRLRL i else stree10LLRLRLRR (i - 15)

def stree10LLRLRL (i : Nat) : State := if i < 31 then stree10LLRLRLL i else stree10LLRLRLR (i - 31)

def stree10LLRLRRLLL (i : Nat) : State := match i with | 0 => state10_679 | 1 => state10_680 | 2 => state10_681 | 3 => state10_682 | 4 => state10_683 | 5 => state10_684 | _ => state10_685

def stree10LLRLRRLLR (i : Nat) : State := match i with | 0 => state10_686 | 1 => state10_687 | 2 => state10_688 | 3 => state10_689 | 4 => state10_690 | 5 => state10_691 | 6 => state10_692 | _ => state10_693

def stree10LLRLRRLL (i : Nat) : State := if i < 7 then stree10LLRLRRLLL i else stree10LLRLRRLLR (i - 7)

def stree10LLRLRRLRL (i : Nat) : State := match i with | 0 => state10_694 | 1 => state10_695 | 2 => state10_696 | 3 => state10_697 | 4 => state10_698 | 5 => state10_699 | 6 => state10_700 | _ => state10_701

def stree10LLRLRRLRR (i : Nat) : State := match i with | 0 => state10_702 | 1 => state10_703 | 2 => state10_704 | 3 => state10_705 | 4 => state10_706 | 5 => state10_707 | 6 => state10_708 | _ => state10_709

def stree10LLRLRRLR (i : Nat) : State := if i < 8 then stree10LLRLRRLRL i else stree10LLRLRRLRR (i - 8)

def stree10LLRLRRL (i : Nat) : State := if i < 15 then stree10LLRLRRLL i else stree10LLRLRRLR (i - 15)

def stree10LLRLRRRLL (i : Nat) : State := match i with | 0 => state10_710 | 1 => state10_711 | 2 => state10_712 | 3 => state10_713 | 4 => state10_714 | 5 => state10_715 | _ => state10_716

def stree10LLRLRRRLR (i : Nat) : State := match i with | 0 => state10_717 | 1 => state10_718 | 2 => state10_719 | 3 => state10_720 | 4 => state10_721 | 5 => state10_722 | 6 => state10_723 | _ => state10_724

def stree10LLRLRRRL (i : Nat) : State := if i < 7 then stree10LLRLRRRLL i else stree10LLRLRRRLR (i - 7)

def stree10LLRLRRRRL (i : Nat) : State := match i with | 0 => state10_725 | 1 => state10_726 | 2 => state10_727 | 3 => state10_728 | 4 => state10_729 | 5 => state10_730 | 6 => state10_731 | _ => state10_732

def stree10LLRLRRRRR (i : Nat) : State := match i with | 0 => state10_733 | 1 => state10_734 | 2 => state10_735 | 3 => state10_736 | 4 => state10_737 | 5 => state10_738 | 6 => state10_739 | _ => state10_740

def stree10LLRLRRRR (i : Nat) : State := if i < 8 then stree10LLRLRRRRL i else stree10LLRLRRRRR (i - 8)

def stree10LLRLRRR (i : Nat) : State := if i < 15 then stree10LLRLRRRL i else stree10LLRLRRRR (i - 15)

def stree10LLRLRR (i : Nat) : State := if i < 31 then stree10LLRLRRL i else stree10LLRLRRR (i - 31)

def stree10LLRLR (i : Nat) : State := if i < 62 then stree10LLRLRL i else stree10LLRLRR (i - 62)

def stree10LLRL (i : Nat) : State := if i < 123 then stree10LLRLL i else stree10LLRLR (i - 123)

def stree10LLRRLLLLL (i : Nat) : State := match i with | 0 => state10_741 | 1 => state10_742 | 2 => state10_743 | 3 => state10_744 | 4 => state10_745 | 5 => state10_746 | _ => state10_747

def stree10LLRRLLLLR (i : Nat) : State := match i with | 0 => state10_748 | 1 => state10_749 | 2 => state10_750 | 3 => state10_751 | 4 => state10_752 | 5 => state10_753 | 6 => state10_754 | _ => state10_755

def stree10LLRRLLLL (i : Nat) : State := if i < 7 then stree10LLRRLLLLL i else stree10LLRRLLLLR (i - 7)

def stree10LLRRLLLRL (i : Nat) : State := match i with | 0 => state10_756 | 1 => state10_757 | 2 => state10_758 | 3 => state10_759 | 4 => state10_760 | 5 => state10_761 | 6 => state10_762 | _ => state10_763

def stree10LLRRLLLRR (i : Nat) : State := match i with | 0 => state10_764 | 1 => state10_765 | 2 => state10_766 | 3 => state10_767 | 4 => state10_768 | 5 => state10_769 | 6 => state10_770 | _ => state10_771

def stree10LLRRLLLR (i : Nat) : State := if i < 8 then stree10LLRRLLLRL i else stree10LLRRLLLRR (i - 8)

def stree10LLRRLLL (i : Nat) : State := if i < 15 then stree10LLRRLLLL i else stree10LLRRLLLR (i - 15)

def stree10LLRRLLRLL (i : Nat) : State := match i with | 0 => state10_772 | 1 => state10_773 | 2 => state10_774 | 3 => state10_775 | 4 => state10_776 | 5 => state10_777 | _ => state10_778

def stree10LLRRLLRLR (i : Nat) : State := match i with | 0 => state10_779 | 1 => state10_780 | 2 => state10_781 | 3 => state10_782 | 4 => state10_783 | 5 => state10_784 | 6 => state10_785 | _ => state10_786

def stree10LLRRLLRL (i : Nat) : State := if i < 7 then stree10LLRRLLRLL i else stree10LLRRLLRLR (i - 7)

def stree10LLRRLLRRL (i : Nat) : State := match i with | 0 => state10_787 | 1 => state10_788 | 2 => state10_789 | 3 => state10_790 | 4 => state10_791 | 5 => state10_792 | 6 => state10_793 | _ => state10_794

def stree10LLRRLLRRR (i : Nat) : State := match i with | 0 => state10_795 | 1 => state10_796 | 2 => state10_797 | 3 => state10_798 | 4 => state10_799 | 5 => state10_800 | 6 => state10_801 | _ => state10_802

def stree10LLRRLLRR (i : Nat) : State := if i < 8 then stree10LLRRLLRRL i else stree10LLRRLLRRR (i - 8)

def stree10LLRRLLR (i : Nat) : State := if i < 15 then stree10LLRRLLRL i else stree10LLRRLLRR (i - 15)

def stree10LLRRLL (i : Nat) : State := if i < 31 then stree10LLRRLLL i else stree10LLRRLLR (i - 31)

def stree10LLRRLRLLL (i : Nat) : State := match i with | 0 => state10_803 | 1 => state10_804 | 2 => state10_805 | 3 => state10_806 | 4 => state10_807 | 5 => state10_808 | _ => state10_809

def stree10LLRRLRLLR (i : Nat) : State := match i with | 0 => state10_810 | 1 => state10_811 | 2 => state10_812 | 3 => state10_813 | 4 => state10_814 | 5 => state10_815 | 6 => state10_816 | _ => state10_817

def stree10LLRRLRLL (i : Nat) : State := if i < 7 then stree10LLRRLRLLL i else stree10LLRRLRLLR (i - 7)

def stree10LLRRLRLRL (i : Nat) : State := match i with | 0 => state10_818 | 1 => state10_819 | 2 => state10_820 | 3 => state10_821 | 4 => state10_822 | 5 => state10_823 | 6 => state10_824 | _ => state10_825

def stree10LLRRLRLRR (i : Nat) : State := match i with | 0 => state10_826 | 1 => state10_827 | 2 => state10_828 | 3 => state10_829 | 4 => state10_830 | 5 => state10_831 | 6 => state10_832 | _ => state10_833

def stree10LLRRLRLR (i : Nat) : State := if i < 8 then stree10LLRRLRLRL i else stree10LLRRLRLRR (i - 8)

def stree10LLRRLRL (i : Nat) : State := if i < 15 then stree10LLRRLRLL i else stree10LLRRLRLR (i - 15)

def stree10LLRRLRRLL (i : Nat) : State := match i with | 0 => state10_834 | 1 => state10_835 | 2 => state10_836 | 3 => state10_837 | 4 => state10_838 | 5 => state10_839 | _ => state10_840

def stree10LLRRLRRLR (i : Nat) : State := match i with | 0 => state10_841 | 1 => state10_842 | 2 => state10_843 | 3 => state10_844 | 4 => state10_845 | 5 => state10_846 | 6 => state10_847 | _ => state10_848

def stree10LLRRLRRL (i : Nat) : State := if i < 7 then stree10LLRRLRRLL i else stree10LLRRLRRLR (i - 7)

def stree10LLRRLRRRL (i : Nat) : State := match i with | 0 => state10_849 | 1 => state10_850 | 2 => state10_851 | 3 => state10_852 | 4 => state10_853 | 5 => state10_854 | 6 => state10_855 | _ => state10_856

def stree10LLRRLRRRR (i : Nat) : State := match i with | 0 => state10_857 | 1 => state10_858 | 2 => state10_859 | 3 => state10_860 | 4 => state10_861 | 5 => state10_862 | 6 => state10_863 | _ => state10_864

def stree10LLRRLRRR (i : Nat) : State := if i < 8 then stree10LLRRLRRRL i else stree10LLRRLRRRR (i - 8)

def stree10LLRRLRR (i : Nat) : State := if i < 15 then stree10LLRRLRRL i else stree10LLRRLRRR (i - 15)

def stree10LLRRLR (i : Nat) : State := if i < 31 then stree10LLRRLRL i else stree10LLRRLRR (i - 31)

def stree10LLRRL (i : Nat) : State := if i < 62 then stree10LLRRLL i else stree10LLRRLR (i - 62)

def stree10LLRRRLLLL (i : Nat) : State := match i with | 0 => state10_865 | 1 => state10_866 | 2 => state10_867 | 3 => state10_868 | 4 => state10_869 | 5 => state10_870 | _ => state10_871

def stree10LLRRRLLLR (i : Nat) : State := match i with | 0 => state10_872 | 1 => state10_873 | 2 => state10_874 | 3 => state10_875 | 4 => state10_876 | 5 => state10_877 | 6 => state10_878 | _ => state10_879

def stree10LLRRRLLL (i : Nat) : State := if i < 7 then stree10LLRRRLLLL i else stree10LLRRRLLLR (i - 7)

def stree10LLRRRLLRL (i : Nat) : State := match i with | 0 => state10_880 | 1 => state10_881 | 2 => state10_882 | 3 => state10_883 | 4 => state10_884 | 5 => state10_885 | 6 => state10_886 | _ => state10_887

def stree10LLRRRLLRR (i : Nat) : State := match i with | 0 => state10_888 | 1 => state10_889 | 2 => state10_890 | 3 => state10_891 | 4 => state10_892 | 5 => state10_893 | 6 => state10_894 | _ => state10_895

def stree10LLRRRLLR (i : Nat) : State := if i < 8 then stree10LLRRRLLRL i else stree10LLRRRLLRR (i - 8)

def stree10LLRRRLL (i : Nat) : State := if i < 15 then stree10LLRRRLLL i else stree10LLRRRLLR (i - 15)

def stree10LLRRRLRLL (i : Nat) : State := match i with | 0 => state10_896 | 1 => state10_897 | 2 => state10_898 | 3 => state10_899 | 4 => state10_900 | 5 => state10_901 | _ => state10_902

def stree10LLRRRLRLR (i : Nat) : State := match i with | 0 => state10_903 | 1 => state10_904 | 2 => state10_905 | 3 => state10_906 | 4 => state10_907 | 5 => state10_908 | 6 => state10_909 | _ => state10_910

def stree10LLRRRLRL (i : Nat) : State := if i < 7 then stree10LLRRRLRLL i else stree10LLRRRLRLR (i - 7)

def stree10LLRRRLRRL (i : Nat) : State := match i with | 0 => state10_911 | 1 => state10_912 | 2 => state10_913 | 3 => state10_914 | 4 => state10_915 | 5 => state10_916 | 6 => state10_917 | _ => state10_918

def stree10LLRRRLRRR (i : Nat) : State := match i with | 0 => state10_919 | 1 => state10_920 | 2 => state10_921 | 3 => state10_922 | 4 => state10_923 | 5 => state10_924 | 6 => state10_925 | _ => state10_926

def stree10LLRRRLRR (i : Nat) : State := if i < 8 then stree10LLRRRLRRL i else stree10LLRRRLRRR (i - 8)

def stree10LLRRRLR (i : Nat) : State := if i < 15 then stree10LLRRRLRL i else stree10LLRRRLRR (i - 15)

def stree10LLRRRL (i : Nat) : State := if i < 31 then stree10LLRRRLL i else stree10LLRRRLR (i - 31)

def stree10LLRRRRLLL (i : Nat) : State := match i with | 0 => state10_927 | 1 => state10_928 | 2 => state10_929 | 3 => state10_930 | 4 => state10_931 | 5 => state10_932 | _ => state10_933

def stree10LLRRRRLLR (i : Nat) : State := match i with | 0 => state10_934 | 1 => state10_935 | 2 => state10_936 | 3 => state10_937 | 4 => state10_938 | 5 => state10_939 | 6 => state10_940 | _ => state10_941

def stree10LLRRRRLL (i : Nat) : State := if i < 7 then stree10LLRRRRLLL i else stree10LLRRRRLLR (i - 7)

def stree10LLRRRRLRL (i : Nat) : State := match i with | 0 => state10_942 | 1 => state10_943 | 2 => state10_944 | 3 => state10_945 | 4 => state10_946 | 5 => state10_947 | 6 => state10_948 | _ => state10_949

def stree10LLRRRRLRR (i : Nat) : State := match i with | 0 => state10_950 | 1 => state10_951 | 2 => state10_952 | 3 => state10_953 | 4 => state10_954 | 5 => state10_955 | 6 => state10_956 | _ => state10_957

def stree10LLRRRRLR (i : Nat) : State := if i < 8 then stree10LLRRRRLRL i else stree10LLRRRRLRR (i - 8)

def stree10LLRRRRL (i : Nat) : State := if i < 15 then stree10LLRRRRLL i else stree10LLRRRRLR (i - 15)

def stree10LLRRRRRLL (i : Nat) : State := match i with | 0 => state10_958 | 1 => state10_959 | 2 => state10_960 | 3 => state10_961 | 4 => state10_962 | 5 => state10_963 | _ => state10_964

def stree10LLRRRRRLR (i : Nat) : State := match i with | 0 => state10_965 | 1 => state10_966 | 2 => state10_967 | 3 => state10_968 | 4 => state10_969 | 5 => state10_970 | 6 => state10_971 | _ => state10_972

def stree10LLRRRRRL (i : Nat) : State := if i < 7 then stree10LLRRRRRLL i else stree10LLRRRRRLR (i - 7)

def stree10LLRRRRRRL (i : Nat) : State := match i with | 0 => state10_973 | 1 => state10_974 | 2 => state10_975 | 3 => state10_976 | 4 => state10_977 | 5 => state10_978 | 6 => state10_979 | _ => state10_980

def stree10LLRRRRRRR (i : Nat) : State := match i with | 0 => state10_981 | 1 => state10_982 | 2 => state10_983 | 3 => state10_984 | 4 => state10_985 | 5 => state10_986 | 6 => state10_987 | _ => state10_988

def stree10LLRRRRRR (i : Nat) : State := if i < 8 then stree10LLRRRRRRL i else stree10LLRRRRRRR (i - 8)

def stree10LLRRRRR (i : Nat) : State := if i < 15 then stree10LLRRRRRL i else stree10LLRRRRRR (i - 15)

def stree10LLRRRR (i : Nat) : State := if i < 31 then stree10LLRRRRL i else stree10LLRRRRR (i - 31)

def stree10LLRRR (i : Nat) : State := if i < 62 then stree10LLRRRL i else stree10LLRRRR (i - 62)

def stree10LLRR (i : Nat) : State := if i < 124 then stree10LLRRL i else stree10LLRRR (i - 124)

def stree10LLR (i : Nat) : State := if i < 247 then stree10LLRL i else stree10LLRR (i - 247)

def stree10LL (i : Nat) : State := if i < 494 then stree10LLL i else stree10LLR (i - 494)

def stree10LRLLLLLLL (i : Nat) : State := match i with | 0 => state10_989 | 1 => state10_990 | 2 => state10_991 | 3 => state10_992 | 4 => state10_993 | 5 => state10_994 | _ => state10_995

def stree10LRLLLLLLR (i : Nat) : State := match i with | 0 => state10_996 | 1 => state10_997 | 2 => state10_998 | 3 => state10_999 | 4 => state10_1000 | 5 => state10_1001 | 6 => state10_1002 | _ => state10_1003

def stree10LRLLLLLL (i : Nat) : State := if i < 7 then stree10LRLLLLLLL i else stree10LRLLLLLLR (i - 7)

def stree10LRLLLLLRL (i : Nat) : State := match i with | 0 => state10_1004 | 1 => state10_1005 | 2 => state10_1006 | 3 => state10_1007 | 4 => state10_1008 | 5 => state10_1009 | _ => state10_1010

def stree10LRLLLLLRR (i : Nat) : State := match i with | 0 => state10_1011 | 1 => state10_1012 | 2 => state10_1013 | 3 => state10_1014 | 4 => state10_1015 | 5 => state10_1016 | 6 => state10_1017 | _ => state10_1018

def stree10LRLLLLLR (i : Nat) : State := if i < 7 then stree10LRLLLLLRL i else stree10LRLLLLLRR (i - 7)

def stree10LRLLLLL (i : Nat) : State := if i < 15 then stree10LRLLLLLL i else stree10LRLLLLLR (i - 15)

def stree10LRLLLLRLL (i : Nat) : State := match i with | 0 => state10_1019 | 1 => state10_1020 | 2 => state10_1021 | 3 => state10_1022 | 4 => state10_1023 | 5 => state10_1024 | _ => state10_1025

def stree10LRLLLLRLR (i : Nat) : State := match i with | 0 => state10_1026 | 1 => state10_1027 | 2 => state10_1028 | 3 => state10_1029 | 4 => state10_1030 | 5 => state10_1031 | 6 => state10_1032 | _ => state10_1033

def stree10LRLLLLRL (i : Nat) : State := if i < 7 then stree10LRLLLLRLL i else stree10LRLLLLRLR (i - 7)

def stree10LRLLLLRRL (i : Nat) : State := match i with | 0 => state10_1034 | 1 => state10_1035 | 2 => state10_1036 | 3 => state10_1037 | 4 => state10_1038 | 5 => state10_1039 | 6 => state10_1040 | _ => state10_1041

def stree10LRLLLLRRR (i : Nat) : State := match i with | 0 => state10_1042 | 1 => state10_1043 | 2 => state10_1044 | 3 => state10_1045 | 4 => state10_1046 | 5 => state10_1047 | 6 => state10_1048 | _ => state10_1049

def stree10LRLLLLRR (i : Nat) : State := if i < 8 then stree10LRLLLLRRL i else stree10LRLLLLRRR (i - 8)

def stree10LRLLLLR (i : Nat) : State := if i < 15 then stree10LRLLLLRL i else stree10LRLLLLRR (i - 15)

def stree10LRLLLL (i : Nat) : State := if i < 30 then stree10LRLLLLL i else stree10LRLLLLR (i - 30)

def stree10LRLLLRLLL (i : Nat) : State := match i with | 0 => state10_1050 | 1 => state10_1051 | 2 => state10_1052 | 3 => state10_1053 | 4 => state10_1054 | 5 => state10_1055 | _ => state10_1056

def stree10LRLLLRLLR (i : Nat) : State := match i with | 0 => state10_1057 | 1 => state10_1058 | 2 => state10_1059 | 3 => state10_1060 | 4 => state10_1061 | 5 => state10_1062 | 6 => state10_1063 | _ => state10_1064

def stree10LRLLLRLL (i : Nat) : State := if i < 7 then stree10LRLLLRLLL i else stree10LRLLLRLLR (i - 7)

def stree10LRLLLRLRL (i : Nat) : State := match i with | 0 => state10_1065 | 1 => state10_1066 | 2 => state10_1067 | 3 => state10_1068 | 4 => state10_1069 | 5 => state10_1070 | 6 => state10_1071 | _ => state10_1072

def stree10LRLLLRLRR (i : Nat) : State := match i with | 0 => state10_1073 | 1 => state10_1074 | 2 => state10_1075 | 3 => state10_1076 | 4 => state10_1077 | 5 => state10_1078 | 6 => state10_1079 | _ => state10_1080

def stree10LRLLLRLR (i : Nat) : State := if i < 8 then stree10LRLLLRLRL i else stree10LRLLLRLRR (i - 8)

def stree10LRLLLRL (i : Nat) : State := if i < 15 then stree10LRLLLRLL i else stree10LRLLLRLR (i - 15)

def stree10LRLLLRRLL (i : Nat) : State := match i with | 0 => state10_1081 | 1 => state10_1082 | 2 => state10_1083 | 3 => state10_1084 | 4 => state10_1085 | 5 => state10_1086 | _ => state10_1087

def stree10LRLLLRRLR (i : Nat) : State := match i with | 0 => state10_1088 | 1 => state10_1089 | 2 => state10_1090 | 3 => state10_1091 | 4 => state10_1092 | 5 => state10_1093 | 6 => state10_1094 | _ => state10_1095

def stree10LRLLLRRL (i : Nat) : State := if i < 7 then stree10LRLLLRRLL i else stree10LRLLLRRLR (i - 7)

def stree10LRLLLRRRL (i : Nat) : State := match i with | 0 => state10_1096 | 1 => state10_1097 | 2 => state10_1098 | 3 => state10_1099 | 4 => state10_1100 | 5 => state10_1101 | 6 => state10_1102 | _ => state10_1103

def stree10LRLLLRRRR (i : Nat) : State := match i with | 0 => state10_1104 | 1 => state10_1105 | 2 => state10_1106 | 3 => state10_1107 | 4 => state10_1108 | 5 => state10_1109 | 6 => state10_1110 | _ => state10_1111

def stree10LRLLLRRR (i : Nat) : State := if i < 8 then stree10LRLLLRRRL i else stree10LRLLLRRRR (i - 8)

def stree10LRLLLRR (i : Nat) : State := if i < 15 then stree10LRLLLRRL i else stree10LRLLLRRR (i - 15)

def stree10LRLLLR (i : Nat) : State := if i < 31 then stree10LRLLLRL i else stree10LRLLLRR (i - 31)

def stree10LRLLL (i : Nat) : State := if i < 61 then stree10LRLLLL i else stree10LRLLLR (i - 61)

def stree10LRLLRLLLL (i : Nat) : State := match i with | 0 => state10_1112 | 1 => state10_1113 | 2 => state10_1114 | 3 => state10_1115 | 4 => state10_1116 | 5 => state10_1117 | _ => state10_1118

def stree10LRLLRLLLR (i : Nat) : State := match i with | 0 => state10_1119 | 1 => state10_1120 | 2 => state10_1121 | 3 => state10_1122 | 4 => state10_1123 | 5 => state10_1124 | 6 => state10_1125 | _ => state10_1126

def stree10LRLLRLLL (i : Nat) : State := if i < 7 then stree10LRLLRLLLL i else stree10LRLLRLLLR (i - 7)

def stree10LRLLRLLRL (i : Nat) : State := match i with | 0 => state10_1127 | 1 => state10_1128 | 2 => state10_1129 | 3 => state10_1130 | 4 => state10_1131 | 5 => state10_1132 | 6 => state10_1133 | _ => state10_1134

def stree10LRLLRLLRR (i : Nat) : State := match i with | 0 => state10_1135 | 1 => state10_1136 | 2 => state10_1137 | 3 => state10_1138 | 4 => state10_1139 | 5 => state10_1140 | 6 => state10_1141 | _ => state10_1142

def stree10LRLLRLLR (i : Nat) : State := if i < 8 then stree10LRLLRLLRL i else stree10LRLLRLLRR (i - 8)

def stree10LRLLRLL (i : Nat) : State := if i < 15 then stree10LRLLRLLL i else stree10LRLLRLLR (i - 15)

def stree10LRLLRLRLL (i : Nat) : State := match i with | 0 => state10_1143 | 1 => state10_1144 | 2 => state10_1145 | 3 => state10_1146 | 4 => state10_1147 | 5 => state10_1148 | _ => state10_1149

def stree10LRLLRLRLR (i : Nat) : State := match i with | 0 => state10_1150 | 1 => state10_1151 | 2 => state10_1152 | 3 => state10_1153 | 4 => state10_1154 | 5 => state10_1155 | 6 => state10_1156 | _ => state10_1157

def stree10LRLLRLRL (i : Nat) : State := if i < 7 then stree10LRLLRLRLL i else stree10LRLLRLRLR (i - 7)

def stree10LRLLRLRRL (i : Nat) : State := match i with | 0 => state10_1158 | 1 => state10_1159 | 2 => state10_1160 | 3 => state10_1161 | 4 => state10_1162 | 5 => state10_1163 | 6 => state10_1164 | _ => state10_1165

def stree10LRLLRLRRR (i : Nat) : State := match i with | 0 => state10_1166 | 1 => state10_1167 | 2 => state10_1168 | 3 => state10_1169 | 4 => state10_1170 | 5 => state10_1171 | 6 => state10_1172 | _ => state10_1173

def stree10LRLLRLRR (i : Nat) : State := if i < 8 then stree10LRLLRLRRL i else stree10LRLLRLRRR (i - 8)

def stree10LRLLRLR (i : Nat) : State := if i < 15 then stree10LRLLRLRL i else stree10LRLLRLRR (i - 15)

def stree10LRLLRL (i : Nat) : State := if i < 31 then stree10LRLLRLL i else stree10LRLLRLR (i - 31)

def stree10LRLLRRLLL (i : Nat) : State := match i with | 0 => state10_1174 | 1 => state10_1175 | 2 => state10_1176 | 3 => state10_1177 | 4 => state10_1178 | 5 => state10_1179 | _ => state10_1180

def stree10LRLLRRLLR (i : Nat) : State := match i with | 0 => state10_1181 | 1 => state10_1182 | 2 => state10_1183 | 3 => state10_1184 | 4 => state10_1185 | 5 => state10_1186 | 6 => state10_1187 | _ => state10_1188

def stree10LRLLRRLL (i : Nat) : State := if i < 7 then stree10LRLLRRLLL i else stree10LRLLRRLLR (i - 7)

def stree10LRLLRRLRL (i : Nat) : State := match i with | 0 => state10_1189 | 1 => state10_1190 | 2 => state10_1191 | 3 => state10_1192 | 4 => state10_1193 | 5 => state10_1194 | 6 => state10_1195 | _ => state10_1196

def stree10LRLLRRLRR (i : Nat) : State := match i with | 0 => state10_1197 | 1 => state10_1198 | 2 => state10_1199 | 3 => state10_1200 | 4 => state10_1201 | 5 => state10_1202 | 6 => state10_1203 | _ => state10_1204

def stree10LRLLRRLR (i : Nat) : State := if i < 8 then stree10LRLLRRLRL i else stree10LRLLRRLRR (i - 8)

def stree10LRLLRRL (i : Nat) : State := if i < 15 then stree10LRLLRRLL i else stree10LRLLRRLR (i - 15)

def stree10LRLLRRRLL (i : Nat) : State := match i with | 0 => state10_1205 | 1 => state10_1206 | 2 => state10_1207 | 3 => state10_1208 | 4 => state10_1209 | 5 => state10_1210 | _ => state10_1211

def stree10LRLLRRRLR (i : Nat) : State := match i with | 0 => state10_1212 | 1 => state10_1213 | 2 => state10_1214 | 3 => state10_1215 | 4 => state10_1216 | 5 => state10_1217 | 6 => state10_1218 | _ => state10_1219

def stree10LRLLRRRL (i : Nat) : State := if i < 7 then stree10LRLLRRRLL i else stree10LRLLRRRLR (i - 7)

def stree10LRLLRRRRL (i : Nat) : State := match i with | 0 => state10_1220 | 1 => state10_1221 | 2 => state10_1222 | 3 => state10_1223 | 4 => state10_1224 | 5 => state10_1225 | 6 => state10_1226 | _ => state10_1227

def stree10LRLLRRRRR (i : Nat) : State := match i with | 0 => state10_1228 | 1 => state10_1229 | 2 => state10_1230 | 3 => state10_1231 | 4 => state10_1232 | 5 => state10_1233 | 6 => state10_1234 | _ => state10_1235

def stree10LRLLRRRR (i : Nat) : State := if i < 8 then stree10LRLLRRRRL i else stree10LRLLRRRRR (i - 8)

def stree10LRLLRRR (i : Nat) : State := if i < 15 then stree10LRLLRRRL i else stree10LRLLRRRR (i - 15)

def stree10LRLLRR (i : Nat) : State := if i < 31 then stree10LRLLRRL i else stree10LRLLRRR (i - 31)

def stree10LRLLR (i : Nat) : State := if i < 62 then stree10LRLLRL i else stree10LRLLRR (i - 62)

def stree10LRLL (i : Nat) : State := if i < 123 then stree10LRLLL i else stree10LRLLR (i - 123)

def stree10LRLRLLLLL (i : Nat) : State := match i with | 0 => state10_1236 | 1 => state10_1237 | 2 => state10_1238 | 3 => state10_1239 | 4 => state10_1240 | 5 => state10_1241 | _ => state10_1242

def stree10LRLRLLLLR (i : Nat) : State := match i with | 0 => state10_1243 | 1 => state10_1244 | 2 => state10_1245 | 3 => state10_1246 | 4 => state10_1247 | 5 => state10_1248 | 6 => state10_1249 | _ => state10_1250

def stree10LRLRLLLL (i : Nat) : State := if i < 7 then stree10LRLRLLLLL i else stree10LRLRLLLLR (i - 7)

def stree10LRLRLLLRL (i : Nat) : State := match i with | 0 => state10_1251 | 1 => state10_1252 | 2 => state10_1253 | 3 => state10_1254 | 4 => state10_1255 | 5 => state10_1256 | 6 => state10_1257 | _ => state10_1258

def stree10LRLRLLLRR (i : Nat) : State := match i with | 0 => state10_1259 | 1 => state10_1260 | 2 => state10_1261 | 3 => state10_1262 | 4 => state10_1263 | 5 => state10_1264 | 6 => state10_1265 | _ => state10_1266

def stree10LRLRLLLR (i : Nat) : State := if i < 8 then stree10LRLRLLLRL i else stree10LRLRLLLRR (i - 8)

def stree10LRLRLLL (i : Nat) : State := if i < 15 then stree10LRLRLLLL i else stree10LRLRLLLR (i - 15)

def stree10LRLRLLRLL (i : Nat) : State := match i with | 0 => state10_1267 | 1 => state10_1268 | 2 => state10_1269 | 3 => state10_1270 | 4 => state10_1271 | 5 => state10_1272 | _ => state10_1273

def stree10LRLRLLRLR (i : Nat) : State := match i with | 0 => state10_1274 | 1 => state10_1275 | 2 => state10_1276 | 3 => state10_1277 | 4 => state10_1278 | 5 => state10_1279 | 6 => state10_1280 | _ => state10_1281

def stree10LRLRLLRL (i : Nat) : State := if i < 7 then stree10LRLRLLRLL i else stree10LRLRLLRLR (i - 7)

def stree10LRLRLLRRL (i : Nat) : State := match i with | 0 => state10_1282 | 1 => state10_1283 | 2 => state10_1284 | 3 => state10_1285 | 4 => state10_1286 | 5 => state10_1287 | 6 => state10_1288 | _ => state10_1289

def stree10LRLRLLRRR (i : Nat) : State := match i with | 0 => state10_1290 | 1 => state10_1291 | 2 => state10_1292 | 3 => state10_1293 | 4 => state10_1294 | 5 => state10_1295 | 6 => state10_1296 | _ => state10_1297

def stree10LRLRLLRR (i : Nat) : State := if i < 8 then stree10LRLRLLRRL i else stree10LRLRLLRRR (i - 8)

def stree10LRLRLLR (i : Nat) : State := if i < 15 then stree10LRLRLLRL i else stree10LRLRLLRR (i - 15)

def stree10LRLRLL (i : Nat) : State := if i < 31 then stree10LRLRLLL i else stree10LRLRLLR (i - 31)

def stree10LRLRLRLLL (i : Nat) : State := match i with | 0 => state10_1298 | 1 => state10_1299 | 2 => state10_1300 | 3 => state10_1301 | 4 => state10_1302 | 5 => state10_1303 | _ => state10_1304

def stree10LRLRLRLLR (i : Nat) : State := match i with | 0 => state10_1305 | 1 => state10_1306 | 2 => state10_1307 | 3 => state10_1308 | 4 => state10_1309 | 5 => state10_1310 | 6 => state10_1311 | _ => state10_1312

def stree10LRLRLRLL (i : Nat) : State := if i < 7 then stree10LRLRLRLLL i else stree10LRLRLRLLR (i - 7)

def stree10LRLRLRLRL (i : Nat) : State := match i with | 0 => state10_1313 | 1 => state10_1314 | 2 => state10_1315 | 3 => state10_1316 | 4 => state10_1317 | 5 => state10_1318 | 6 => state10_1319 | _ => state10_1320

def stree10LRLRLRLRR (i : Nat) : State := match i with | 0 => state10_1321 | 1 => state10_1322 | 2 => state10_1323 | 3 => state10_1324 | 4 => state10_1325 | 5 => state10_1326 | 6 => state10_1327 | _ => state10_1328

def stree10LRLRLRLR (i : Nat) : State := if i < 8 then stree10LRLRLRLRL i else stree10LRLRLRLRR (i - 8)

def stree10LRLRLRL (i : Nat) : State := if i < 15 then stree10LRLRLRLL i else stree10LRLRLRLR (i - 15)

def stree10LRLRLRRLL (i : Nat) : State := match i with | 0 => state10_1329 | 1 => state10_1330 | 2 => state10_1331 | 3 => state10_1332 | 4 => state10_1333 | 5 => state10_1334 | _ => state10_1335

def stree10LRLRLRRLR (i : Nat) : State := match i with | 0 => state10_1336 | 1 => state10_1337 | 2 => state10_1338 | 3 => state10_1339 | 4 => state10_1340 | 5 => state10_1341 | 6 => state10_1342 | _ => state10_1343

def stree10LRLRLRRL (i : Nat) : State := if i < 7 then stree10LRLRLRRLL i else stree10LRLRLRRLR (i - 7)

def stree10LRLRLRRRL (i : Nat) : State := match i with | 0 => state10_1344 | 1 => state10_1345 | 2 => state10_1346 | 3 => state10_1347 | 4 => state10_1348 | 5 => state10_1349 | 6 => state10_1350 | _ => state10_1351

def stree10LRLRLRRRR (i : Nat) : State := match i with | 0 => state10_1352 | 1 => state10_1353 | 2 => state10_1354 | 3 => state10_1355 | 4 => state10_1356 | 5 => state10_1357 | 6 => state10_1358 | _ => state10_1359

def stree10LRLRLRRR (i : Nat) : State := if i < 8 then stree10LRLRLRRRL i else stree10LRLRLRRRR (i - 8)

def stree10LRLRLRR (i : Nat) : State := if i < 15 then stree10LRLRLRRL i else stree10LRLRLRRR (i - 15)

def stree10LRLRLR (i : Nat) : State := if i < 31 then stree10LRLRLRL i else stree10LRLRLRR (i - 31)

def stree10LRLRL (i : Nat) : State := if i < 62 then stree10LRLRLL i else stree10LRLRLR (i - 62)

def stree10LRLRRLLLL (i : Nat) : State := match i with | 0 => state10_1360 | 1 => state10_1361 | 2 => state10_1362 | 3 => state10_1363 | 4 => state10_1364 | 5 => state10_1365 | _ => state10_1366

def stree10LRLRRLLLR (i : Nat) : State := match i with | 0 => state10_1367 | 1 => state10_1368 | 2 => state10_1369 | 3 => state10_1370 | 4 => state10_1371 | 5 => state10_1372 | 6 => state10_1373 | _ => state10_1374

def stree10LRLRRLLL (i : Nat) : State := if i < 7 then stree10LRLRRLLLL i else stree10LRLRRLLLR (i - 7)

def stree10LRLRRLLRL (i : Nat) : State := match i with | 0 => state10_1375 | 1 => state10_1376 | 2 => state10_1377 | 3 => state10_1378 | 4 => state10_1379 | 5 => state10_1380 | 6 => state10_1381 | _ => state10_1382

def stree10LRLRRLLRR (i : Nat) : State := match i with | 0 => state10_1383 | 1 => state10_1384 | 2 => state10_1385 | 3 => state10_1386 | 4 => state10_1387 | 5 => state10_1388 | 6 => state10_1389 | _ => state10_1390

def stree10LRLRRLLR (i : Nat) : State := if i < 8 then stree10LRLRRLLRL i else stree10LRLRRLLRR (i - 8)

def stree10LRLRRLL (i : Nat) : State := if i < 15 then stree10LRLRRLLL i else stree10LRLRRLLR (i - 15)

def stree10LRLRRLRLL (i : Nat) : State := match i with | 0 => state10_1391 | 1 => state10_1392 | 2 => state10_1393 | 3 => state10_1394 | 4 => state10_1395 | 5 => state10_1396 | _ => state10_1397

def stree10LRLRRLRLR (i : Nat) : State := match i with | 0 => state10_1398 | 1 => state10_1399 | 2 => state10_1400 | 3 => state10_1401 | 4 => state10_1402 | 5 => state10_1403 | 6 => state10_1404 | _ => state10_1405

def stree10LRLRRLRL (i : Nat) : State := if i < 7 then stree10LRLRRLRLL i else stree10LRLRRLRLR (i - 7)

def stree10LRLRRLRRL (i : Nat) : State := match i with | 0 => state10_1406 | 1 => state10_1407 | 2 => state10_1408 | 3 => state10_1409 | 4 => state10_1410 | 5 => state10_1411 | 6 => state10_1412 | _ => state10_1413

def stree10LRLRRLRRR (i : Nat) : State := match i with | 0 => state10_1414 | 1 => state10_1415 | 2 => state10_1416 | 3 => state10_1417 | 4 => state10_1418 | 5 => state10_1419 | 6 => state10_1420 | _ => state10_1421

def stree10LRLRRLRR (i : Nat) : State := if i < 8 then stree10LRLRRLRRL i else stree10LRLRRLRRR (i - 8)

def stree10LRLRRLR (i : Nat) : State := if i < 15 then stree10LRLRRLRL i else stree10LRLRRLRR (i - 15)

def stree10LRLRRL (i : Nat) : State := if i < 31 then stree10LRLRRLL i else stree10LRLRRLR (i - 31)

def stree10LRLRRRLLL (i : Nat) : State := match i with | 0 => state10_1422 | 1 => state10_1423 | 2 => state10_1424 | 3 => state10_1425 | 4 => state10_1426 | 5 => state10_1427 | _ => state10_1428

def stree10LRLRRRLLR (i : Nat) : State := match i with | 0 => state10_1429 | 1 => state10_1430 | 2 => state10_1431 | 3 => state10_1432 | 4 => state10_1433 | 5 => state10_1434 | 6 => state10_1435 | _ => state10_1436

def stree10LRLRRRLL (i : Nat) : State := if i < 7 then stree10LRLRRRLLL i else stree10LRLRRRLLR (i - 7)

def stree10LRLRRRLRL (i : Nat) : State := match i with | 0 => state10_1437 | 1 => state10_1438 | 2 => state10_1439 | 3 => state10_1440 | 4 => state10_1441 | 5 => state10_1442 | 6 => state10_1443 | _ => state10_1444

def stree10LRLRRRLRR (i : Nat) : State := match i with | 0 => state10_1445 | 1 => state10_1446 | 2 => state10_1447 | 3 => state10_1448 | 4 => state10_1449 | 5 => state10_1450 | 6 => state10_1451 | _ => state10_1452

def stree10LRLRRRLR (i : Nat) : State := if i < 8 then stree10LRLRRRLRL i else stree10LRLRRRLRR (i - 8)

def stree10LRLRRRL (i : Nat) : State := if i < 15 then stree10LRLRRRLL i else stree10LRLRRRLR (i - 15)

def stree10LRLRRRRLL (i : Nat) : State := match i with | 0 => state10_1453 | 1 => state10_1454 | 2 => state10_1455 | 3 => state10_1456 | 4 => state10_1457 | 5 => state10_1458 | _ => state10_1459

def stree10LRLRRRRLR (i : Nat) : State := match i with | 0 => state10_1460 | 1 => state10_1461 | 2 => state10_1462 | 3 => state10_1463 | 4 => state10_1464 | 5 => state10_1465 | 6 => state10_1466 | _ => state10_1467

def stree10LRLRRRRL (i : Nat) : State := if i < 7 then stree10LRLRRRRLL i else stree10LRLRRRRLR (i - 7)

def stree10LRLRRRRRL (i : Nat) : State := match i with | 0 => state10_1468 | 1 => state10_1469 | 2 => state10_1470 | 3 => state10_1471 | 4 => state10_1472 | 5 => state10_1473 | 6 => state10_1474 | _ => state10_1475

def stree10LRLRRRRRR (i : Nat) : State := match i with | 0 => state10_1476 | 1 => state10_1477 | 2 => state10_1478 | 3 => state10_1479 | 4 => state10_1480 | 5 => state10_1481 | 6 => state10_1482 | _ => state10_1483

def stree10LRLRRRRR (i : Nat) : State := if i < 8 then stree10LRLRRRRRL i else stree10LRLRRRRRR (i - 8)

def stree10LRLRRRR (i : Nat) : State := if i < 15 then stree10LRLRRRRL i else stree10LRLRRRRR (i - 15)

def stree10LRLRRR (i : Nat) : State := if i < 31 then stree10LRLRRRL i else stree10LRLRRRR (i - 31)

def stree10LRLRR (i : Nat) : State := if i < 62 then stree10LRLRRL i else stree10LRLRRR (i - 62)

def stree10LRLR (i : Nat) : State := if i < 124 then stree10LRLRL i else stree10LRLRR (i - 124)

def stree10LRL (i : Nat) : State := if i < 247 then stree10LRLL i else stree10LRLR (i - 247)

def stree10LRRLLLLLL (i : Nat) : State := match i with | 0 => state10_1484 | 1 => state10_1485 | 2 => state10_1486 | 3 => state10_1487 | 4 => state10_1488 | 5 => state10_1489 | _ => state10_1490

def stree10LRRLLLLLR (i : Nat) : State := match i with | 0 => state10_1491 | 1 => state10_1492 | 2 => state10_1493 | 3 => state10_1494 | 4 => state10_1495 | 5 => state10_1496 | 6 => state10_1497 | _ => state10_1498

def stree10LRRLLLLL (i : Nat) : State := if i < 7 then stree10LRRLLLLLL i else stree10LRRLLLLLR (i - 7)

def stree10LRRLLLLRL (i : Nat) : State := match i with | 0 => state10_1499 | 1 => state10_1500 | 2 => state10_1501 | 3 => state10_1502 | 4 => state10_1503 | 5 => state10_1504 | _ => state10_1505

def stree10LRRLLLLRR (i : Nat) : State := match i with | 0 => state10_1506 | 1 => state10_1507 | 2 => state10_1508 | 3 => state10_1509 | 4 => state10_1510 | 5 => state10_1511 | 6 => state10_1512 | _ => state10_1513

def stree10LRRLLLLR (i : Nat) : State := if i < 7 then stree10LRRLLLLRL i else stree10LRRLLLLRR (i - 7)

def stree10LRRLLLL (i : Nat) : State := if i < 15 then stree10LRRLLLLL i else stree10LRRLLLLR (i - 15)

def stree10LRRLLLRLL (i : Nat) : State := match i with | 0 => state10_1514 | 1 => state10_1515 | 2 => state10_1516 | 3 => state10_1517 | 4 => state10_1518 | 5 => state10_1519 | _ => state10_1520

def stree10LRRLLLRLR (i : Nat) : State := match i with | 0 => state10_1521 | 1 => state10_1522 | 2 => state10_1523 | 3 => state10_1524 | 4 => state10_1525 | 5 => state10_1526 | 6 => state10_1527 | _ => state10_1528

def stree10LRRLLLRL (i : Nat) : State := if i < 7 then stree10LRRLLLRLL i else stree10LRRLLLRLR (i - 7)

def stree10LRRLLLRRL (i : Nat) : State := match i with | 0 => state10_1529 | 1 => state10_1530 | 2 => state10_1531 | 3 => state10_1532 | 4 => state10_1533 | 5 => state10_1534 | 6 => state10_1535 | _ => state10_1536

def stree10LRRLLLRRR (i : Nat) : State := match i with | 0 => state10_1537 | 1 => state10_1538 | 2 => state10_1539 | 3 => state10_1540 | 4 => state10_1541 | 5 => state10_1542 | 6 => state10_1543 | _ => state10_1544

def stree10LRRLLLRR (i : Nat) : State := if i < 8 then stree10LRRLLLRRL i else stree10LRRLLLRRR (i - 8)

def stree10LRRLLLR (i : Nat) : State := if i < 15 then stree10LRRLLLRL i else stree10LRRLLLRR (i - 15)

def stree10LRRLLL (i : Nat) : State := if i < 30 then stree10LRRLLLL i else stree10LRRLLLR (i - 30)

def stree10LRRLLRLLL (i : Nat) : State := match i with | 0 => state10_1545 | 1 => state10_1546 | 2 => state10_1547 | 3 => state10_1548 | 4 => state10_1549 | 5 => state10_1550 | _ => state10_1551

def stree10LRRLLRLLR (i : Nat) : State := match i with | 0 => state10_1552 | 1 => state10_1553 | 2 => state10_1554 | 3 => state10_1555 | 4 => state10_1556 | 5 => state10_1557 | 6 => state10_1558 | _ => state10_1559

def stree10LRRLLRLL (i : Nat) : State := if i < 7 then stree10LRRLLRLLL i else stree10LRRLLRLLR (i - 7)

def stree10LRRLLRLRL (i : Nat) : State := match i with | 0 => state10_1560 | 1 => state10_1561 | 2 => state10_1562 | 3 => state10_1563 | 4 => state10_1564 | 5 => state10_1565 | 6 => state10_1566 | _ => state10_1567

def stree10LRRLLRLRR (i : Nat) : State := match i with | 0 => state10_1568 | 1 => state10_1569 | 2 => state10_1570 | 3 => state10_1571 | 4 => state10_1572 | 5 => state10_1573 | 6 => state10_1574 | _ => state10_1575

def stree10LRRLLRLR (i : Nat) : State := if i < 8 then stree10LRRLLRLRL i else stree10LRRLLRLRR (i - 8)

def stree10LRRLLRL (i : Nat) : State := if i < 15 then stree10LRRLLRLL i else stree10LRRLLRLR (i - 15)

def stree10LRRLLRRLL (i : Nat) : State := match i with | 0 => state10_1576 | 1 => state10_1577 | 2 => state10_1578 | 3 => state10_1579 | 4 => state10_1580 | 5 => state10_1581 | _ => state10_1582

def stree10LRRLLRRLR (i : Nat) : State := match i with | 0 => state10_1583 | 1 => state10_1584 | 2 => state10_1585 | 3 => state10_1586 | 4 => state10_1587 | 5 => state10_1588 | 6 => state10_1589 | _ => state10_1590

def stree10LRRLLRRL (i : Nat) : State := if i < 7 then stree10LRRLLRRLL i else stree10LRRLLRRLR (i - 7)

def stree10LRRLLRRRL (i : Nat) : State := match i with | 0 => state10_1591 | 1 => state10_1592 | 2 => state10_1593 | 3 => state10_1594 | 4 => state10_1595 | 5 => state10_1596 | 6 => state10_1597 | _ => state10_1598

def stree10LRRLLRRRR (i : Nat) : State := match i with | 0 => state10_1599 | 1 => state10_1600 | 2 => state10_1601 | 3 => state10_1602 | 4 => state10_1603 | 5 => state10_1604 | 6 => state10_1605 | _ => state10_1606

def stree10LRRLLRRR (i : Nat) : State := if i < 8 then stree10LRRLLRRRL i else stree10LRRLLRRRR (i - 8)

def stree10LRRLLRR (i : Nat) : State := if i < 15 then stree10LRRLLRRL i else stree10LRRLLRRR (i - 15)

def stree10LRRLLR (i : Nat) : State := if i < 31 then stree10LRRLLRL i else stree10LRRLLRR (i - 31)

def stree10LRRLL (i : Nat) : State := if i < 61 then stree10LRRLLL i else stree10LRRLLR (i - 61)

def stree10LRRLRLLLL (i : Nat) : State := match i with | 0 => state10_1607 | 1 => state10_1608 | 2 => state10_1609 | 3 => state10_1610 | 4 => state10_1611 | 5 => state10_1612 | _ => state10_1613

def stree10LRRLRLLLR (i : Nat) : State := match i with | 0 => state10_1614 | 1 => state10_1615 | 2 => state10_1616 | 3 => state10_1617 | 4 => state10_1618 | 5 => state10_1619 | 6 => state10_1620 | _ => state10_1621

def stree10LRRLRLLL (i : Nat) : State := if i < 7 then stree10LRRLRLLLL i else stree10LRRLRLLLR (i - 7)

def stree10LRRLRLLRL (i : Nat) : State := match i with | 0 => state10_1622 | 1 => state10_1623 | 2 => state10_1624 | 3 => state10_1625 | 4 => state10_1626 | 5 => state10_1627 | 6 => state10_1628 | _ => state10_1629

def stree10LRRLRLLRR (i : Nat) : State := match i with | 0 => state10_1630 | 1 => state10_1631 | 2 => state10_1632 | 3 => state10_1633 | 4 => state10_1634 | 5 => state10_1635 | 6 => state10_1636 | _ => state10_1637

def stree10LRRLRLLR (i : Nat) : State := if i < 8 then stree10LRRLRLLRL i else stree10LRRLRLLRR (i - 8)

def stree10LRRLRLL (i : Nat) : State := if i < 15 then stree10LRRLRLLL i else stree10LRRLRLLR (i - 15)

def stree10LRRLRLRLL (i : Nat) : State := match i with | 0 => state10_1638 | 1 => state10_1639 | 2 => state10_1640 | 3 => state10_1641 | 4 => state10_1642 | 5 => state10_1643 | _ => state10_1644

def stree10LRRLRLRLR (i : Nat) : State := match i with | 0 => state10_1645 | 1 => state10_1646 | 2 => state10_1647 | 3 => state10_1648 | 4 => state10_1649 | 5 => state10_1650 | 6 => state10_1651 | _ => state10_1652

def stree10LRRLRLRL (i : Nat) : State := if i < 7 then stree10LRRLRLRLL i else stree10LRRLRLRLR (i - 7)

def stree10LRRLRLRRL (i : Nat) : State := match i with | 0 => state10_1653 | 1 => state10_1654 | 2 => state10_1655 | 3 => state10_1656 | 4 => state10_1657 | 5 => state10_1658 | 6 => state10_1659 | _ => state10_1660

def stree10LRRLRLRRR (i : Nat) : State := match i with | 0 => state10_1661 | 1 => state10_1662 | 2 => state10_1663 | 3 => state10_1664 | 4 => state10_1665 | 5 => state10_1666 | 6 => state10_1667 | _ => state10_1668

def stree10LRRLRLRR (i : Nat) : State := if i < 8 then stree10LRRLRLRRL i else stree10LRRLRLRRR (i - 8)

def stree10LRRLRLR (i : Nat) : State := if i < 15 then stree10LRRLRLRL i else stree10LRRLRLRR (i - 15)

def stree10LRRLRL (i : Nat) : State := if i < 31 then stree10LRRLRLL i else stree10LRRLRLR (i - 31)

def stree10LRRLRRLLL (i : Nat) : State := match i with | 0 => state10_1669 | 1 => state10_1670 | 2 => state10_1671 | 3 => state10_1672 | 4 => state10_1673 | 5 => state10_1674 | _ => state10_1675

def stree10LRRLRRLLR (i : Nat) : State := match i with | 0 => state10_1676 | 1 => state10_1677 | 2 => state10_1678 | 3 => state10_1679 | 4 => state10_1680 | 5 => state10_1681 | 6 => state10_1682 | _ => state10_1683

def stree10LRRLRRLL (i : Nat) : State := if i < 7 then stree10LRRLRRLLL i else stree10LRRLRRLLR (i - 7)

def stree10LRRLRRLRL (i : Nat) : State := match i with | 0 => state10_1684 | 1 => state10_1685 | 2 => state10_1686 | 3 => state10_1687 | 4 => state10_1688 | 5 => state10_1689 | 6 => state10_1690 | _ => state10_1691

def stree10LRRLRRLRR (i : Nat) : State := match i with | 0 => state10_1692 | 1 => state10_1693 | 2 => state10_1694 | 3 => state10_1695 | 4 => state10_1696 | 5 => state10_1697 | 6 => state10_1698 | _ => state10_1699

def stree10LRRLRRLR (i : Nat) : State := if i < 8 then stree10LRRLRRLRL i else stree10LRRLRRLRR (i - 8)

def stree10LRRLRRL (i : Nat) : State := if i < 15 then stree10LRRLRRLL i else stree10LRRLRRLR (i - 15)

def stree10LRRLRRRLL (i : Nat) : State := match i with | 0 => state10_1700 | 1 => state10_1701 | 2 => state10_1702 | 3 => state10_1703 | 4 => state10_1704 | 5 => state10_1705 | _ => state10_1706

def stree10LRRLRRRLR (i : Nat) : State := match i with | 0 => state10_1707 | 1 => state10_1708 | 2 => state10_1709 | 3 => state10_1710 | 4 => state10_1711 | 5 => state10_1712 | 6 => state10_1713 | _ => state10_1714

def stree10LRRLRRRL (i : Nat) : State := if i < 7 then stree10LRRLRRRLL i else stree10LRRLRRRLR (i - 7)

def stree10LRRLRRRRL (i : Nat) : State := match i with | 0 => state10_1715 | 1 => state10_1716 | 2 => state10_1717 | 3 => state10_1718 | 4 => state10_1719 | 5 => state10_1720 | 6 => state10_1721 | _ => state10_1722

def stree10LRRLRRRRR (i : Nat) : State := match i with | 0 => state10_1723 | 1 => state10_1724 | 2 => state10_1725 | 3 => state10_1726 | 4 => state10_1727 | 5 => state10_1728 | 6 => state10_1729 | _ => state10_1730

def stree10LRRLRRRR (i : Nat) : State := if i < 8 then stree10LRRLRRRRL i else stree10LRRLRRRRR (i - 8)

def stree10LRRLRRR (i : Nat) : State := if i < 15 then stree10LRRLRRRL i else stree10LRRLRRRR (i - 15)

def stree10LRRLRR (i : Nat) : State := if i < 31 then stree10LRRLRRL i else stree10LRRLRRR (i - 31)

def stree10LRRLR (i : Nat) : State := if i < 62 then stree10LRRLRL i else stree10LRRLRR (i - 62)

def stree10LRRL (i : Nat) : State := if i < 123 then stree10LRRLL i else stree10LRRLR (i - 123)

def stree10LRRRLLLLL (i : Nat) : State := match i with | 0 => state10_1731 | 1 => state10_1732 | 2 => state10_1733 | 3 => state10_1734 | 4 => state10_1735 | 5 => state10_1736 | _ => state10_1737

def stree10LRRRLLLLR (i : Nat) : State := match i with | 0 => state10_1738 | 1 => state10_1739 | 2 => state10_1740 | 3 => state10_1741 | 4 => state10_1742 | 5 => state10_1743 | 6 => state10_1744 | _ => state10_1745

def stree10LRRRLLLL (i : Nat) : State := if i < 7 then stree10LRRRLLLLL i else stree10LRRRLLLLR (i - 7)

def stree10LRRRLLLRL (i : Nat) : State := match i with | 0 => state10_1746 | 1 => state10_1747 | 2 => state10_1748 | 3 => state10_1749 | 4 => state10_1750 | 5 => state10_1751 | 6 => state10_1752 | _ => state10_1753

def stree10LRRRLLLRR (i : Nat) : State := match i with | 0 => state10_1754 | 1 => state10_1755 | 2 => state10_1756 | 3 => state10_1757 | 4 => state10_1758 | 5 => state10_1759 | 6 => state10_1760 | _ => state10_1761

def stree10LRRRLLLR (i : Nat) : State := if i < 8 then stree10LRRRLLLRL i else stree10LRRRLLLRR (i - 8)

def stree10LRRRLLL (i : Nat) : State := if i < 15 then stree10LRRRLLLL i else stree10LRRRLLLR (i - 15)

def stree10LRRRLLRLL (i : Nat) : State := match i with | 0 => state10_1762 | 1 => state10_1763 | 2 => state10_1764 | 3 => state10_1765 | 4 => state10_1766 | 5 => state10_1767 | _ => state10_1768

def stree10LRRRLLRLR (i : Nat) : State := match i with | 0 => state10_1769 | 1 => state10_1770 | 2 => state10_1771 | 3 => state10_1772 | 4 => state10_1773 | 5 => state10_1774 | 6 => state10_1775 | _ => state10_1776

def stree10LRRRLLRL (i : Nat) : State := if i < 7 then stree10LRRRLLRLL i else stree10LRRRLLRLR (i - 7)

def stree10LRRRLLRRL (i : Nat) : State := match i with | 0 => state10_1777 | 1 => state10_1778 | 2 => state10_1779 | 3 => state10_1780 | 4 => state10_1781 | 5 => state10_1782 | 6 => state10_1783 | _ => state10_1784

def stree10LRRRLLRRR (i : Nat) : State := match i with | 0 => state10_1785 | 1 => state10_1786 | 2 => state10_1787 | 3 => state10_1788 | 4 => state10_1789 | 5 => state10_1790 | 6 => state10_1791 | _ => state10_1792

def stree10LRRRLLRR (i : Nat) : State := if i < 8 then stree10LRRRLLRRL i else stree10LRRRLLRRR (i - 8)

def stree10LRRRLLR (i : Nat) : State := if i < 15 then stree10LRRRLLRL i else stree10LRRRLLRR (i - 15)

def stree10LRRRLL (i : Nat) : State := if i < 31 then stree10LRRRLLL i else stree10LRRRLLR (i - 31)

def stree10LRRRLRLLL (i : Nat) : State := match i with | 0 => state10_1793 | 1 => state10_1794 | 2 => state10_1795 | 3 => state10_1796 | 4 => state10_1797 | 5 => state10_1798 | _ => state10_1799

def stree10LRRRLRLLR (i : Nat) : State := match i with | 0 => state10_1800 | 1 => state10_1801 | 2 => state10_1802 | 3 => state10_1803 | 4 => state10_1804 | 5 => state10_1805 | 6 => state10_1806 | _ => state10_1807

def stree10LRRRLRLL (i : Nat) : State := if i < 7 then stree10LRRRLRLLL i else stree10LRRRLRLLR (i - 7)

def stree10LRRRLRLRL (i : Nat) : State := match i with | 0 => state10_1808 | 1 => state10_1809 | 2 => state10_1810 | 3 => state10_1811 | 4 => state10_1812 | 5 => state10_1813 | 6 => state10_1814 | _ => state10_1815

def stree10LRRRLRLRR (i : Nat) : State := match i with | 0 => state10_1816 | 1 => state10_1817 | 2 => state10_1818 | 3 => state10_1819 | 4 => state10_1820 | 5 => state10_1821 | 6 => state10_1822 | _ => state10_1823

def stree10LRRRLRLR (i : Nat) : State := if i < 8 then stree10LRRRLRLRL i else stree10LRRRLRLRR (i - 8)

def stree10LRRRLRL (i : Nat) : State := if i < 15 then stree10LRRRLRLL i else stree10LRRRLRLR (i - 15)

def stree10LRRRLRRLL (i : Nat) : State := match i with | 0 => state10_1824 | 1 => state10_1825 | 2 => state10_1826 | 3 => state10_1827 | 4 => state10_1828 | 5 => state10_1829 | _ => state10_1830

def stree10LRRRLRRLR (i : Nat) : State := match i with | 0 => state10_1831 | 1 => state10_1832 | 2 => state10_1833 | 3 => state10_1834 | 4 => state10_1835 | 5 => state10_1836 | 6 => state10_1837 | _ => state10_1838

def stree10LRRRLRRL (i : Nat) : State := if i < 7 then stree10LRRRLRRLL i else stree10LRRRLRRLR (i - 7)

def stree10LRRRLRRRL (i : Nat) : State := match i with | 0 => state10_1839 | 1 => state10_1840 | 2 => state10_1841 | 3 => state10_1842 | 4 => state10_1843 | 5 => state10_1844 | 6 => state10_1845 | _ => state10_1846

def stree10LRRRLRRRR (i : Nat) : State := match i with | 0 => state10_1847 | 1 => state10_1848 | 2 => state10_1849 | 3 => state10_1850 | 4 => state10_1851 | 5 => state10_1852 | 6 => state10_1853 | _ => state10_1854

def stree10LRRRLRRR (i : Nat) : State := if i < 8 then stree10LRRRLRRRL i else stree10LRRRLRRRR (i - 8)

def stree10LRRRLRR (i : Nat) : State := if i < 15 then stree10LRRRLRRL i else stree10LRRRLRRR (i - 15)

def stree10LRRRLR (i : Nat) : State := if i < 31 then stree10LRRRLRL i else stree10LRRRLRR (i - 31)

def stree10LRRRL (i : Nat) : State := if i < 62 then stree10LRRRLL i else stree10LRRRLR (i - 62)

def stree10LRRRRLLLL (i : Nat) : State := match i with | 0 => state10_1855 | 1 => state10_1856 | 2 => state10_1857 | 3 => state10_1858 | 4 => state10_1859 | 5 => state10_1860 | _ => state10_1861

def stree10LRRRRLLLR (i : Nat) : State := match i with | 0 => state10_1862 | 1 => state10_1863 | 2 => state10_1864 | 3 => state10_1865 | 4 => state10_1866 | 5 => state10_1867 | 6 => state10_1868 | _ => state10_1869

def stree10LRRRRLLL (i : Nat) : State := if i < 7 then stree10LRRRRLLLL i else stree10LRRRRLLLR (i - 7)

def stree10LRRRRLLRL (i : Nat) : State := match i with | 0 => state10_1870 | 1 => state10_1871 | 2 => state10_1872 | 3 => state10_1873 | 4 => state10_1874 | 5 => state10_1875 | 6 => state10_1876 | _ => state10_1877

def stree10LRRRRLLRR (i : Nat) : State := match i with | 0 => state10_1878 | 1 => state10_1879 | 2 => state10_1880 | 3 => state10_1881 | 4 => state10_1882 | 5 => state10_1883 | 6 => state10_1884 | _ => state10_1885

def stree10LRRRRLLR (i : Nat) : State := if i < 8 then stree10LRRRRLLRL i else stree10LRRRRLLRR (i - 8)

def stree10LRRRRLL (i : Nat) : State := if i < 15 then stree10LRRRRLLL i else stree10LRRRRLLR (i - 15)

def stree10LRRRRLRLL (i : Nat) : State := match i with | 0 => state10_1886 | 1 => state10_1887 | 2 => state10_1888 | 3 => state10_1889 | 4 => state10_1890 | 5 => state10_1891 | _ => state10_1892

def stree10LRRRRLRLR (i : Nat) : State := match i with | 0 => state10_1893 | 1 => state10_1894 | 2 => state10_1895 | 3 => state10_1896 | 4 => state10_1897 | 5 => state10_1898 | 6 => state10_1899 | _ => state10_1900

def stree10LRRRRLRL (i : Nat) : State := if i < 7 then stree10LRRRRLRLL i else stree10LRRRRLRLR (i - 7)

def stree10LRRRRLRRL (i : Nat) : State := match i with | 0 => state10_1901 | 1 => state10_1902 | 2 => state10_1903 | 3 => state10_1904 | 4 => state10_1905 | 5 => state10_1906 | 6 => state10_1907 | _ => state10_1908

def stree10LRRRRLRRR (i : Nat) : State := match i with | 0 => state10_1909 | 1 => state10_1910 | 2 => state10_1911 | 3 => state10_1912 | 4 => state10_1913 | 5 => state10_1914 | 6 => state10_1915 | _ => state10_1916

def stree10LRRRRLRR (i : Nat) : State := if i < 8 then stree10LRRRRLRRL i else stree10LRRRRLRRR (i - 8)

def stree10LRRRRLR (i : Nat) : State := if i < 15 then stree10LRRRRLRL i else stree10LRRRRLRR (i - 15)

def stree10LRRRRL (i : Nat) : State := if i < 31 then stree10LRRRRLL i else stree10LRRRRLR (i - 31)

def stree10LRRRRRLLL (i : Nat) : State := match i with | 0 => state10_1917 | 1 => state10_1918 | 2 => state10_1919 | 3 => state10_1920 | 4 => state10_1921 | 5 => state10_1922 | _ => state10_1923

def stree10LRRRRRLLR (i : Nat) : State := match i with | 0 => state10_1924 | 1 => state10_1925 | 2 => state10_1926 | 3 => state10_1927 | 4 => state10_1928 | 5 => state10_1929 | 6 => state10_1930 | _ => state10_1931

def stree10LRRRRRLL (i : Nat) : State := if i < 7 then stree10LRRRRRLLL i else stree10LRRRRRLLR (i - 7)

def stree10LRRRRRLRL (i : Nat) : State := match i with | 0 => state10_1932 | 1 => state10_1933 | 2 => state10_1934 | 3 => state10_1935 | 4 => state10_1936 | 5 => state10_1937 | 6 => state10_1938 | _ => state10_1939

def stree10LRRRRRLRR (i : Nat) : State := match i with | 0 => state10_1940 | 1 => state10_1941 | 2 => state10_1942 | 3 => state10_1943 | 4 => state10_1944 | 5 => state10_1945 | 6 => state10_1946 | _ => state10_1947

def stree10LRRRRRLR (i : Nat) : State := if i < 8 then stree10LRRRRRLRL i else stree10LRRRRRLRR (i - 8)

def stree10LRRRRRL (i : Nat) : State := if i < 15 then stree10LRRRRRLL i else stree10LRRRRRLR (i - 15)

def stree10LRRRRRRLL (i : Nat) : State := match i with | 0 => state10_1948 | 1 => state10_1949 | 2 => state10_1950 | 3 => state10_1951 | 4 => state10_1952 | 5 => state10_1953 | _ => state10_1954

def stree10LRRRRRRLR (i : Nat) : State := match i with | 0 => state10_1955 | 1 => state10_1956 | 2 => state10_1957 | 3 => state10_1958 | 4 => state10_1959 | 5 => state10_1960 | 6 => state10_1961 | _ => state10_1962

def stree10LRRRRRRL (i : Nat) : State := if i < 7 then stree10LRRRRRRLL i else stree10LRRRRRRLR (i - 7)

def stree10LRRRRRRRL (i : Nat) : State := match i with | 0 => state10_1963 | 1 => state10_1964 | 2 => state10_1965 | 3 => state10_1966 | 4 => state10_1967 | 5 => state10_1968 | 6 => state10_1969 | _ => state10_1970

def stree10LRRRRRRRR (i : Nat) : State := match i with | 0 => state10_1971 | 1 => state10_1972 | 2 => state10_1973 | 3 => state10_1974 | 4 => state10_1975 | 5 => state10_1976 | 6 => state10_1977 | _ => state10_1978

def stree10LRRRRRRR (i : Nat) : State := if i < 8 then stree10LRRRRRRRL i else stree10LRRRRRRRR (i - 8)

def stree10LRRRRRR (i : Nat) : State := if i < 15 then stree10LRRRRRRL i else stree10LRRRRRRR (i - 15)

def stree10LRRRRR (i : Nat) : State := if i < 31 then stree10LRRRRRL i else stree10LRRRRRR (i - 31)

def stree10LRRRR (i : Nat) : State := if i < 62 then stree10LRRRRL i else stree10LRRRRR (i - 62)

def stree10LRRR (i : Nat) : State := if i < 124 then stree10LRRRL i else stree10LRRRR (i - 124)

def stree10LRR (i : Nat) : State := if i < 247 then stree10LRRL i else stree10LRRR (i - 247)

def stree10LR (i : Nat) : State := if i < 495 then stree10LRL i else stree10LRR (i - 495)

def stree10L (i : Nat) : State := if i < 989 then stree10LL i else stree10LR (i - 989)

def stree10RLLLLLLLL (i : Nat) : State := match i with | 0 => state10_1979 | 1 => state10_1980 | 2 => state10_1981 | 3 => state10_1982 | 4 => state10_1983 | 5 => state10_1984 | _ => state10_1985

def stree10RLLLLLLLR (i : Nat) : State := match i with | 0 => state10_1986 | 1 => state10_1987 | 2 => state10_1988 | 3 => state10_1989 | 4 => state10_1990 | 5 => state10_1991 | 6 => state10_1992 | _ => state10_1993

def stree10RLLLLLLL (i : Nat) : State := if i < 7 then stree10RLLLLLLLL i else stree10RLLLLLLLR (i - 7)

def stree10RLLLLLLRL (i : Nat) : State := match i with | 0 => state10_1994 | 1 => state10_1995 | 2 => state10_1996 | 3 => state10_1997 | 4 => state10_1998 | 5 => state10_1999 | _ => state10_2000

def stree10RLLLLLLRR (i : Nat) : State := match i with | 0 => state10_2001 | 1 => state10_2002 | 2 => state10_2003 | 3 => state10_2004 | 4 => state10_2005 | 5 => state10_2006 | 6 => state10_2007 | _ => state10_2008

def stree10RLLLLLLR (i : Nat) : State := if i < 7 then stree10RLLLLLLRL i else stree10RLLLLLLRR (i - 7)

def stree10RLLLLLL (i : Nat) : State := if i < 15 then stree10RLLLLLLL i else stree10RLLLLLLR (i - 15)

def stree10RLLLLLRLL (i : Nat) : State := match i with | 0 => state10_2009 | 1 => state10_2010 | 2 => state10_2011 | 3 => state10_2012 | 4 => state10_2013 | 5 => state10_2014 | _ => state10_2015

def stree10RLLLLLRLR (i : Nat) : State := match i with | 0 => state10_2016 | 1 => state10_2017 | 2 => state10_2018 | 3 => state10_2019 | 4 => state10_2020 | 5 => state10_2021 | 6 => state10_2022 | _ => state10_2023

def stree10RLLLLLRL (i : Nat) : State := if i < 7 then stree10RLLLLLRLL i else stree10RLLLLLRLR (i - 7)

def stree10RLLLLLRRL (i : Nat) : State := match i with | 0 => state10_2024 | 1 => state10_2025 | 2 => state10_2026 | 3 => state10_2027 | 4 => state10_2028 | 5 => state10_2029 | 6 => state10_2030 | _ => state10_2031

def stree10RLLLLLRRR (i : Nat) : State := match i with | 0 => state10_2032 | 1 => state10_2033 | 2 => state10_2034 | 3 => state10_2035 | 4 => state10_2036 | 5 => state10_2037 | 6 => state10_2038 | _ => state10_2039

def stree10RLLLLLRR (i : Nat) : State := if i < 8 then stree10RLLLLLRRL i else stree10RLLLLLRRR (i - 8)

def stree10RLLLLLR (i : Nat) : State := if i < 15 then stree10RLLLLLRL i else stree10RLLLLLRR (i - 15)

def stree10RLLLLL (i : Nat) : State := if i < 30 then stree10RLLLLLL i else stree10RLLLLLR (i - 30)

def stree10RLLLLRLLL (i : Nat) : State := match i with | 0 => state10_2040 | 1 => state10_2041 | 2 => state10_2042 | 3 => state10_2043 | 4 => state10_2044 | 5 => state10_2045 | _ => state10_2046

def stree10RLLLLRLLR (i : Nat) : State := match i with | 0 => state10_2047 | 1 => state10_2048 | 2 => state10_2049 | 3 => state10_2050 | 4 => state10_2051 | 5 => state10_2052 | 6 => state10_2053 | _ => state10_2054

def stree10RLLLLRLL (i : Nat) : State := if i < 7 then stree10RLLLLRLLL i else stree10RLLLLRLLR (i - 7)

def stree10RLLLLRLRL (i : Nat) : State := match i with | 0 => state10_2055 | 1 => state10_2056 | 2 => state10_2057 | 3 => state10_2058 | 4 => state10_2059 | 5 => state10_2060 | 6 => state10_2061 | _ => state10_2062

def stree10RLLLLRLRR (i : Nat) : State := match i with | 0 => state10_2063 | 1 => state10_2064 | 2 => state10_2065 | 3 => state10_2066 | 4 => state10_2067 | 5 => state10_2068 | 6 => state10_2069 | _ => state10_2070

def stree10RLLLLRLR (i : Nat) : State := if i < 8 then stree10RLLLLRLRL i else stree10RLLLLRLRR (i - 8)

def stree10RLLLLRL (i : Nat) : State := if i < 15 then stree10RLLLLRLL i else stree10RLLLLRLR (i - 15)

def stree10RLLLLRRLL (i : Nat) : State := match i with | 0 => state10_2071 | 1 => state10_2072 | 2 => state10_2073 | 3 => state10_2074 | 4 => state10_2075 | 5 => state10_2076 | _ => state10_2077

def stree10RLLLLRRLR (i : Nat) : State := match i with | 0 => state10_2078 | 1 => state10_2079 | 2 => state10_2080 | 3 => state10_2081 | 4 => state10_2082 | 5 => state10_2083 | 6 => state10_2084 | _ => state10_2085

def stree10RLLLLRRL (i : Nat) : State := if i < 7 then stree10RLLLLRRLL i else stree10RLLLLRRLR (i - 7)

def stree10RLLLLRRRL (i : Nat) : State := match i with | 0 => state10_2086 | 1 => state10_2087 | 2 => state10_2088 | 3 => state10_2089 | 4 => state10_2090 | 5 => state10_2091 | 6 => state10_2092 | _ => state10_2093

def stree10RLLLLRRRR (i : Nat) : State := match i with | 0 => state10_2094 | 1 => state10_2095 | 2 => state10_2096 | 3 => state10_2097 | 4 => state10_2098 | 5 => state10_2099 | 6 => state10_2100 | _ => state10_2101

def stree10RLLLLRRR (i : Nat) : State := if i < 8 then stree10RLLLLRRRL i else stree10RLLLLRRRR (i - 8)

def stree10RLLLLRR (i : Nat) : State := if i < 15 then stree10RLLLLRRL i else stree10RLLLLRRR (i - 15)

def stree10RLLLLR (i : Nat) : State := if i < 31 then stree10RLLLLRL i else stree10RLLLLRR (i - 31)

def stree10RLLLL (i : Nat) : State := if i < 61 then stree10RLLLLL i else stree10RLLLLR (i - 61)

def stree10RLLLRLLLL (i : Nat) : State := match i with | 0 => state10_2102 | 1 => state10_2103 | 2 => state10_2104 | 3 => state10_2105 | 4 => state10_2106 | 5 => state10_2107 | _ => state10_2108

def stree10RLLLRLLLR (i : Nat) : State := match i with | 0 => state10_2109 | 1 => state10_2110 | 2 => state10_2111 | 3 => state10_2112 | 4 => state10_2113 | 5 => state10_2114 | 6 => state10_2115 | _ => state10_2116

def stree10RLLLRLLL (i : Nat) : State := if i < 7 then stree10RLLLRLLLL i else stree10RLLLRLLLR (i - 7)

def stree10RLLLRLLRL (i : Nat) : State := match i with | 0 => state10_2117 | 1 => state10_2118 | 2 => state10_2119 | 3 => state10_2120 | 4 => state10_2121 | 5 => state10_2122 | 6 => state10_2123 | _ => state10_2124

def stree10RLLLRLLRR (i : Nat) : State := match i with | 0 => state10_2125 | 1 => state10_2126 | 2 => state10_2127 | 3 => state10_2128 | 4 => state10_2129 | 5 => state10_2130 | 6 => state10_2131 | _ => state10_2132

def stree10RLLLRLLR (i : Nat) : State := if i < 8 then stree10RLLLRLLRL i else stree10RLLLRLLRR (i - 8)

def stree10RLLLRLL (i : Nat) : State := if i < 15 then stree10RLLLRLLL i else stree10RLLLRLLR (i - 15)

def stree10RLLLRLRLL (i : Nat) : State := match i with | 0 => state10_2133 | 1 => state10_2134 | 2 => state10_2135 | 3 => state10_2136 | 4 => state10_2137 | 5 => state10_2138 | _ => state10_2139

def stree10RLLLRLRLR (i : Nat) : State := match i with | 0 => state10_2140 | 1 => state10_2141 | 2 => state10_2142 | 3 => state10_2143 | 4 => state10_2144 | 5 => state10_2145 | 6 => state10_2146 | _ => state10_2147

def stree10RLLLRLRL (i : Nat) : State := if i < 7 then stree10RLLLRLRLL i else stree10RLLLRLRLR (i - 7)

def stree10RLLLRLRRL (i : Nat) : State := match i with | 0 => state10_2148 | 1 => state10_2149 | 2 => state10_2150 | 3 => state10_2151 | 4 => state10_2152 | 5 => state10_2153 | 6 => state10_2154 | _ => state10_2155

def stree10RLLLRLRRR (i : Nat) : State := match i with | 0 => state10_2156 | 1 => state10_2157 | 2 => state10_2158 | 3 => state10_2159 | 4 => state10_2160 | 5 => state10_2161 | 6 => state10_2162 | _ => state10_2163

def stree10RLLLRLRR (i : Nat) : State := if i < 8 then stree10RLLLRLRRL i else stree10RLLLRLRRR (i - 8)

def stree10RLLLRLR (i : Nat) : State := if i < 15 then stree10RLLLRLRL i else stree10RLLLRLRR (i - 15)

def stree10RLLLRL (i : Nat) : State := if i < 31 then stree10RLLLRLL i else stree10RLLLRLR (i - 31)

def stree10RLLLRRLLL (i : Nat) : State := match i with | 0 => state10_2164 | 1 => state10_2165 | 2 => state10_2166 | 3 => state10_2167 | 4 => state10_2168 | 5 => state10_2169 | _ => state10_2170

def stree10RLLLRRLLR (i : Nat) : State := match i with | 0 => state10_2171 | 1 => state10_2172 | 2 => state10_2173 | 3 => state10_2174 | 4 => state10_2175 | 5 => state10_2176 | 6 => state10_2177 | _ => state10_2178

def stree10RLLLRRLL (i : Nat) : State := if i < 7 then stree10RLLLRRLLL i else stree10RLLLRRLLR (i - 7)

def stree10RLLLRRLRL (i : Nat) : State := match i with | 0 => state10_2179 | 1 => state10_2180 | 2 => state10_2181 | 3 => state10_2182 | 4 => state10_2183 | 5 => state10_2184 | 6 => state10_2185 | _ => state10_2186

def stree10RLLLRRLRR (i : Nat) : State := match i with | 0 => state10_2187 | 1 => state10_2188 | 2 => state10_2189 | 3 => state10_2190 | 4 => state10_2191 | 5 => state10_2192 | 6 => state10_2193 | _ => state10_2194

def stree10RLLLRRLR (i : Nat) : State := if i < 8 then stree10RLLLRRLRL i else stree10RLLLRRLRR (i - 8)

def stree10RLLLRRL (i : Nat) : State := if i < 15 then stree10RLLLRRLL i else stree10RLLLRRLR (i - 15)

def stree10RLLLRRRLL (i : Nat) : State := match i with | 0 => state10_2195 | 1 => state10_2196 | 2 => state10_2197 | 3 => state10_2198 | 4 => state10_2199 | 5 => state10_2200 | _ => state10_2201

def stree10RLLLRRRLR (i : Nat) : State := match i with | 0 => state10_2202 | 1 => state10_2203 | 2 => state10_2204 | 3 => state10_2205 | 4 => state10_2206 | 5 => state10_2207 | 6 => state10_2208 | _ => state10_2209

def stree10RLLLRRRL (i : Nat) : State := if i < 7 then stree10RLLLRRRLL i else stree10RLLLRRRLR (i - 7)

def stree10RLLLRRRRL (i : Nat) : State := match i with | 0 => state10_2210 | 1 => state10_2211 | 2 => state10_2212 | 3 => state10_2213 | 4 => state10_2214 | 5 => state10_2215 | 6 => state10_2216 | _ => state10_2217

def stree10RLLLRRRRR (i : Nat) : State := match i with | 0 => state10_2218 | 1 => state10_2219 | 2 => state10_2220 | 3 => state10_2221 | 4 => state10_2222 | 5 => state10_2223 | 6 => state10_2224 | _ => state10_2225

def stree10RLLLRRRR (i : Nat) : State := if i < 8 then stree10RLLLRRRRL i else stree10RLLLRRRRR (i - 8)

def stree10RLLLRRR (i : Nat) : State := if i < 15 then stree10RLLLRRRL i else stree10RLLLRRRR (i - 15)

def stree10RLLLRR (i : Nat) : State := if i < 31 then stree10RLLLRRL i else stree10RLLLRRR (i - 31)

def stree10RLLLR (i : Nat) : State := if i < 62 then stree10RLLLRL i else stree10RLLLRR (i - 62)

def stree10RLLL (i : Nat) : State := if i < 123 then stree10RLLLL i else stree10RLLLR (i - 123)

def stree10RLLRLLLLL (i : Nat) : State := match i with | 0 => state10_2226 | 1 => state10_2227 | 2 => state10_2228 | 3 => state10_2229 | 4 => state10_2230 | 5 => state10_2231 | _ => state10_2232

def stree10RLLRLLLLR (i : Nat) : State := match i with | 0 => state10_2233 | 1 => state10_2234 | 2 => state10_2235 | 3 => state10_2236 | 4 => state10_2237 | 5 => state10_2238 | 6 => state10_2239 | _ => state10_2240

def stree10RLLRLLLL (i : Nat) : State := if i < 7 then stree10RLLRLLLLL i else stree10RLLRLLLLR (i - 7)

def stree10RLLRLLLRL (i : Nat) : State := match i with | 0 => state10_2241 | 1 => state10_2242 | 2 => state10_2243 | 3 => state10_2244 | 4 => state10_2245 | 5 => state10_2246 | 6 => state10_2247 | _ => state10_2248

def stree10RLLRLLLRR (i : Nat) : State := match i with | 0 => state10_2249 | 1 => state10_2250 | 2 => state10_2251 | 3 => state10_2252 | 4 => state10_2253 | 5 => state10_2254 | 6 => state10_2255 | _ => state10_2256

def stree10RLLRLLLR (i : Nat) : State := if i < 8 then stree10RLLRLLLRL i else stree10RLLRLLLRR (i - 8)

def stree10RLLRLLL (i : Nat) : State := if i < 15 then stree10RLLRLLLL i else stree10RLLRLLLR (i - 15)

def stree10RLLRLLRLL (i : Nat) : State := match i with | 0 => state10_2257 | 1 => state10_2258 | 2 => state10_2259 | 3 => state10_2260 | 4 => state10_2261 | 5 => state10_2262 | _ => state10_2263

def stree10RLLRLLRLR (i : Nat) : State := match i with | 0 => state10_2264 | 1 => state10_2265 | 2 => state10_2266 | 3 => state10_2267 | 4 => state10_2268 | 5 => state10_2269 | 6 => state10_2270 | _ => state10_2271

def stree10RLLRLLRL (i : Nat) : State := if i < 7 then stree10RLLRLLRLL i else stree10RLLRLLRLR (i - 7)

def stree10RLLRLLRRL (i : Nat) : State := match i with | 0 => state10_2272 | 1 => state10_2273 | 2 => state10_2274 | 3 => state10_2275 | 4 => state10_2276 | 5 => state10_2277 | 6 => state10_2278 | _ => state10_2279

def stree10RLLRLLRRR (i : Nat) : State := match i with | 0 => state10_2280 | 1 => state10_2281 | 2 => state10_2282 | 3 => state10_2283 | 4 => state10_2284 | 5 => state10_2285 | 6 => state10_2286 | _ => state10_2287

def stree10RLLRLLRR (i : Nat) : State := if i < 8 then stree10RLLRLLRRL i else stree10RLLRLLRRR (i - 8)

def stree10RLLRLLR (i : Nat) : State := if i < 15 then stree10RLLRLLRL i else stree10RLLRLLRR (i - 15)

def stree10RLLRLL (i : Nat) : State := if i < 31 then stree10RLLRLLL i else stree10RLLRLLR (i - 31)

def stree10RLLRLRLLL (i : Nat) : State := match i with | 0 => state10_2288 | 1 => state10_2289 | 2 => state10_2290 | 3 => state10_2291 | 4 => state10_2292 | 5 => state10_2293 | _ => state10_2294

def stree10RLLRLRLLR (i : Nat) : State := match i with | 0 => state10_2295 | 1 => state10_2296 | 2 => state10_2297 | 3 => state10_2298 | 4 => state10_2299 | 5 => state10_2300 | 6 => state10_2301 | _ => state10_2302

def stree10RLLRLRLL (i : Nat) : State := if i < 7 then stree10RLLRLRLLL i else stree10RLLRLRLLR (i - 7)

def stree10RLLRLRLRL (i : Nat) : State := match i with | 0 => state10_2303 | 1 => state10_2304 | 2 => state10_2305 | 3 => state10_2306 | 4 => state10_2307 | 5 => state10_2308 | 6 => state10_2309 | _ => state10_2310

def stree10RLLRLRLRR (i : Nat) : State := match i with | 0 => state10_2311 | 1 => state10_2312 | 2 => state10_2313 | 3 => state10_2314 | 4 => state10_2315 | 5 => state10_2316 | 6 => state10_2317 | _ => state10_2318

def stree10RLLRLRLR (i : Nat) : State := if i < 8 then stree10RLLRLRLRL i else stree10RLLRLRLRR (i - 8)

def stree10RLLRLRL (i : Nat) : State := if i < 15 then stree10RLLRLRLL i else stree10RLLRLRLR (i - 15)

def stree10RLLRLRRLL (i : Nat) : State := match i with | 0 => state10_2319 | 1 => state10_2320 | 2 => state10_2321 | 3 => state10_2322 | 4 => state10_2323 | 5 => state10_2324 | _ => state10_2325

def stree10RLLRLRRLR (i : Nat) : State := match i with | 0 => state10_2326 | 1 => state10_2327 | 2 => state10_2328 | 3 => state10_2329 | 4 => state10_2330 | 5 => state10_2331 | 6 => state10_2332 | _ => state10_2333

def stree10RLLRLRRL (i : Nat) : State := if i < 7 then stree10RLLRLRRLL i else stree10RLLRLRRLR (i - 7)

def stree10RLLRLRRRL (i : Nat) : State := match i with | 0 => state10_2334 | 1 => state10_2335 | 2 => state10_2336 | 3 => state10_2337 | 4 => state10_2338 | 5 => state10_2339 | 6 => state10_2340 | _ => state10_2341

def stree10RLLRLRRRR (i : Nat) : State := match i with | 0 => state10_2342 | 1 => state10_2343 | 2 => state10_2344 | 3 => state10_2345 | 4 => state10_2346 | 5 => state10_2347 | 6 => state10_2348 | _ => state10_2349

def stree10RLLRLRRR (i : Nat) : State := if i < 8 then stree10RLLRLRRRL i else stree10RLLRLRRRR (i - 8)

def stree10RLLRLRR (i : Nat) : State := if i < 15 then stree10RLLRLRRL i else stree10RLLRLRRR (i - 15)

def stree10RLLRLR (i : Nat) : State := if i < 31 then stree10RLLRLRL i else stree10RLLRLRR (i - 31)

def stree10RLLRL (i : Nat) : State := if i < 62 then stree10RLLRLL i else stree10RLLRLR (i - 62)

def stree10RLLRRLLLL (i : Nat) : State := match i with | 0 => state10_2350 | 1 => state10_2351 | 2 => state10_2352 | 3 => state10_2353 | 4 => state10_2354 | 5 => state10_2355 | _ => state10_2356

def stree10RLLRRLLLR (i : Nat) : State := match i with | 0 => state10_2357 | 1 => state10_2358 | 2 => state10_2359 | 3 => state10_2360 | 4 => state10_2361 | 5 => state10_2362 | 6 => state10_2363 | _ => state10_2364

def stree10RLLRRLLL (i : Nat) : State := if i < 7 then stree10RLLRRLLLL i else stree10RLLRRLLLR (i - 7)

def stree10RLLRRLLRL (i : Nat) : State := match i with | 0 => state10_2365 | 1 => state10_2366 | 2 => state10_2367 | 3 => state10_2368 | 4 => state10_2369 | 5 => state10_2370 | 6 => state10_2371 | _ => state10_2372

def stree10RLLRRLLRR (i : Nat) : State := match i with | 0 => state10_2373 | 1 => state10_2374 | 2 => state10_2375 | 3 => state10_2376 | 4 => state10_2377 | 5 => state10_2378 | 6 => state10_2379 | _ => state10_2380

def stree10RLLRRLLR (i : Nat) : State := if i < 8 then stree10RLLRRLLRL i else stree10RLLRRLLRR (i - 8)

def stree10RLLRRLL (i : Nat) : State := if i < 15 then stree10RLLRRLLL i else stree10RLLRRLLR (i - 15)

def stree10RLLRRLRLL (i : Nat) : State := match i with | 0 => state10_2381 | 1 => state10_2382 | 2 => state10_2383 | 3 => state10_2384 | 4 => state10_2385 | 5 => state10_2386 | _ => state10_2387

def stree10RLLRRLRLR (i : Nat) : State := match i with | 0 => state10_2388 | 1 => state10_2389 | 2 => state10_2390 | 3 => state10_2391 | 4 => state10_2392 | 5 => state10_2393 | 6 => state10_2394 | _ => state10_2395

def stree10RLLRRLRL (i : Nat) : State := if i < 7 then stree10RLLRRLRLL i else stree10RLLRRLRLR (i - 7)

def stree10RLLRRLRRL (i : Nat) : State := match i with | 0 => state10_2396 | 1 => state10_2397 | 2 => state10_2398 | 3 => state10_2399 | 4 => state10_2400 | 5 => state10_2401 | 6 => state10_2402 | _ => state10_2403

def stree10RLLRRLRRR (i : Nat) : State := match i with | 0 => state10_2404 | 1 => state10_2405 | 2 => state10_2406 | 3 => state10_2407 | 4 => state10_2408 | 5 => state10_2409 | 6 => state10_2410 | _ => state10_2411

def stree10RLLRRLRR (i : Nat) : State := if i < 8 then stree10RLLRRLRRL i else stree10RLLRRLRRR (i - 8)

def stree10RLLRRLR (i : Nat) : State := if i < 15 then stree10RLLRRLRL i else stree10RLLRRLRR (i - 15)

def stree10RLLRRL (i : Nat) : State := if i < 31 then stree10RLLRRLL i else stree10RLLRRLR (i - 31)

def stree10RLLRRRLLL (i : Nat) : State := match i with | 0 => state10_2412 | 1 => state10_2413 | 2 => state10_2414 | 3 => state10_2415 | 4 => state10_2416 | 5 => state10_2417 | _ => state10_2418

def stree10RLLRRRLLR (i : Nat) : State := match i with | 0 => state10_2419 | 1 => state10_2420 | 2 => state10_2421 | 3 => state10_2422 | 4 => state10_2423 | 5 => state10_2424 | 6 => state10_2425 | _ => state10_2426

def stree10RLLRRRLL (i : Nat) : State := if i < 7 then stree10RLLRRRLLL i else stree10RLLRRRLLR (i - 7)

def stree10RLLRRRLRL (i : Nat) : State := match i with | 0 => state10_2427 | 1 => state10_2428 | 2 => state10_2429 | 3 => state10_2430 | 4 => state10_2431 | 5 => state10_2432 | 6 => state10_2433 | _ => state10_2434

def stree10RLLRRRLRR (i : Nat) : State := match i with | 0 => state10_2435 | 1 => state10_2436 | 2 => state10_2437 | 3 => state10_2438 | 4 => state10_2439 | 5 => state10_2440 | 6 => state10_2441 | _ => state10_2442

def stree10RLLRRRLR (i : Nat) : State := if i < 8 then stree10RLLRRRLRL i else stree10RLLRRRLRR (i - 8)

def stree10RLLRRRL (i : Nat) : State := if i < 15 then stree10RLLRRRLL i else stree10RLLRRRLR (i - 15)

def stree10RLLRRRRLL (i : Nat) : State := match i with | 0 => state10_2443 | 1 => state10_2444 | 2 => state10_2445 | 3 => state10_2446 | 4 => state10_2447 | 5 => state10_2448 | _ => state10_2449

def stree10RLLRRRRLR (i : Nat) : State := match i with | 0 => state10_2450 | 1 => state10_2451 | 2 => state10_2452 | 3 => state10_2453 | 4 => state10_2454 | 5 => state10_2455 | 6 => state10_2456 | _ => state10_2457

def stree10RLLRRRRL (i : Nat) : State := if i < 7 then stree10RLLRRRRLL i else stree10RLLRRRRLR (i - 7)

def stree10RLLRRRRRL (i : Nat) : State := match i with | 0 => state10_2458 | 1 => state10_2459 | 2 => state10_2460 | 3 => state10_2461 | 4 => state10_2462 | 5 => state10_2463 | 6 => state10_2464 | _ => state10_2465

def stree10RLLRRRRRR (i : Nat) : State := match i with | 0 => state10_2466 | 1 => state10_2467 | 2 => state10_2468 | 3 => state10_2469 | 4 => state10_2470 | 5 => state10_2471 | 6 => state10_2472 | _ => state10_2473

def stree10RLLRRRRR (i : Nat) : State := if i < 8 then stree10RLLRRRRRL i else stree10RLLRRRRRR (i - 8)

def stree10RLLRRRR (i : Nat) : State := if i < 15 then stree10RLLRRRRL i else stree10RLLRRRRR (i - 15)

def stree10RLLRRR (i : Nat) : State := if i < 31 then stree10RLLRRRL i else stree10RLLRRRR (i - 31)

def stree10RLLRR (i : Nat) : State := if i < 62 then stree10RLLRRL i else stree10RLLRRR (i - 62)

def stree10RLLR (i : Nat) : State := if i < 124 then stree10RLLRL i else stree10RLLRR (i - 124)

def stree10RLL (i : Nat) : State := if i < 247 then stree10RLLL i else stree10RLLR (i - 247)

def stree10RLRLLLLLL (i : Nat) : State := match i with | 0 => state10_2474 | 1 => state10_2475 | 2 => state10_2476 | 3 => state10_2477 | 4 => state10_2478 | 5 => state10_2479 | _ => state10_2480

def stree10RLRLLLLLR (i : Nat) : State := match i with | 0 => state10_2481 | 1 => state10_2482 | 2 => state10_2483 | 3 => state10_2484 | 4 => state10_2485 | 5 => state10_2486 | 6 => state10_2487 | _ => state10_2488

def stree10RLRLLLLL (i : Nat) : State := if i < 7 then stree10RLRLLLLLL i else stree10RLRLLLLLR (i - 7)

def stree10RLRLLLLRL (i : Nat) : State := match i with | 0 => state10_2489 | 1 => state10_2490 | 2 => state10_2491 | 3 => state10_2492 | 4 => state10_2493 | 5 => state10_2494 | _ => state10_2495

def stree10RLRLLLLRR (i : Nat) : State := match i with | 0 => state10_2496 | 1 => state10_2497 | 2 => state10_2498 | 3 => state10_2499 | 4 => state10_2500 | 5 => state10_2501 | 6 => state10_2502 | _ => state10_2503

def stree10RLRLLLLR (i : Nat) : State := if i < 7 then stree10RLRLLLLRL i else stree10RLRLLLLRR (i - 7)

def stree10RLRLLLL (i : Nat) : State := if i < 15 then stree10RLRLLLLL i else stree10RLRLLLLR (i - 15)

def stree10RLRLLLRLL (i : Nat) : State := match i with | 0 => state10_2504 | 1 => state10_2505 | 2 => state10_2506 | 3 => state10_2507 | 4 => state10_2508 | 5 => state10_2509 | _ => state10_2510

def stree10RLRLLLRLR (i : Nat) : State := match i with | 0 => state10_2511 | 1 => state10_2512 | 2 => state10_2513 | 3 => state10_2514 | 4 => state10_2515 | 5 => state10_2516 | 6 => state10_2517 | _ => state10_2518

def stree10RLRLLLRL (i : Nat) : State := if i < 7 then stree10RLRLLLRLL i else stree10RLRLLLRLR (i - 7)

def stree10RLRLLLRRL (i : Nat) : State := match i with | 0 => state10_2519 | 1 => state10_2520 | 2 => state10_2521 | 3 => state10_2522 | 4 => state10_2523 | 5 => state10_2524 | 6 => state10_2525 | _ => state10_2526

end Paper2.Certificates.Q6.Coverage
