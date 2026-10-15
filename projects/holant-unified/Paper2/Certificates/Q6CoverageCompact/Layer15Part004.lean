import Paper2.Certificates.Q6CoverageCompact.Layer15Part003

namespace Paper2.Certificates.Q6.Coverage

def stree15LRLRRRLL (i : Nat) : State := match i with | 0 => state15_670 | 1 => state15_671 | 2 => state15_672 | 3 => state15_673 | 4 => state15_674 | 5 => state15_675 | _ => state15_676

def stree15LRLRRRLR (i : Nat) : State := match i with | 0 => state15_677 | 1 => state15_678 | 2 => state15_679 | 3 => state15_680 | 4 => state15_681 | 5 => state15_682 | 6 => state15_683 | _ => state15_684

def stree15LRLRRRL (i : Nat) : State := if i < 7 then stree15LRLRRRLL i else stree15LRLRRRLR (i - 7)

def stree15LRLRRRRL (i : Nat) : State := match i with | 0 => state15_685 | 1 => state15_686 | 2 => state15_687 | 3 => state15_688 | 4 => state15_689 | 5 => state15_690 | _ => state15_691

def stree15LRLRRRRR (i : Nat) : State := match i with | 0 => state15_692 | 1 => state15_693 | 2 => state15_694 | 3 => state15_695 | 4 => state15_696 | 5 => state15_697 | 6 => state15_698 | _ => state15_699

def stree15LRLRRRR (i : Nat) : State := if i < 7 then stree15LRLRRRRL i else stree15LRLRRRRR (i - 7)

def stree15LRLRRR (i : Nat) : State := if i < 15 then stree15LRLRRRL i else stree15LRLRRRR (i - 15)

def stree15LRLRR (i : Nat) : State := if i < 29 then stree15LRLRRL i else stree15LRLRRR (i - 29)

def stree15LRLR (i : Nat) : State := if i < 58 then stree15LRLRL i else stree15LRLRR (i - 58)

def stree15LRL (i : Nat) : State := if i < 116 then stree15LRLL i else stree15LRLR (i - 116)

def stree15LRRLLLLL (i : Nat) : State := match i with | 0 => state15_700 | 1 => state15_701 | 2 => state15_702 | 3 => state15_703 | 4 => state15_704 | 5 => state15_705 | _ => state15_706

def stree15LRRLLLLR (i : Nat) : State := match i with | 0 => state15_707 | 1 => state15_708 | 2 => state15_709 | 3 => state15_710 | 4 => state15_711 | 5 => state15_712 | _ => state15_713

def stree15LRRLLLL (i : Nat) : State := if i < 7 then stree15LRRLLLLL i else stree15LRRLLLLR (i - 7)

def stree15LRRLLLRL (i : Nat) : State := match i with | 0 => state15_714 | 1 => state15_715 | 2 => state15_716 | 3 => state15_717 | 4 => state15_718 | 5 => state15_719 | _ => state15_720

def stree15LRRLLLRR (i : Nat) : State := match i with | 0 => state15_721 | 1 => state15_722 | 2 => state15_723 | 3 => state15_724 | 4 => state15_725 | 5 => state15_726 | 6 => state15_727 | _ => state15_728

def stree15LRRLLLR (i : Nat) : State := if i < 7 then stree15LRRLLLRL i else stree15LRRLLLRR (i - 7)

def stree15LRRLLL (i : Nat) : State := if i < 14 then stree15LRRLLLL i else stree15LRRLLLR (i - 14)

def stree15LRRLLRLL (i : Nat) : State := match i with | 0 => state15_729 | 1 => state15_730 | 2 => state15_731 | 3 => state15_732 | 4 => state15_733 | 5 => state15_734 | _ => state15_735

def stree15LRRLLRLR (i : Nat) : State := match i with | 0 => state15_736 | 1 => state15_737 | 2 => state15_738 | 3 => state15_739 | 4 => state15_740 | 5 => state15_741 | _ => state15_742

def stree15LRRLLRL (i : Nat) : State := if i < 7 then stree15LRRLLRLL i else stree15LRRLLRLR (i - 7)

def stree15LRRLLRRL (i : Nat) : State := match i with | 0 => state15_743 | 1 => state15_744 | 2 => state15_745 | 3 => state15_746 | 4 => state15_747 | 5 => state15_748 | _ => state15_749

def stree15LRRLLRRR (i : Nat) : State := match i with | 0 => state15_750 | 1 => state15_751 | 2 => state15_752 | 3 => state15_753 | 4 => state15_754 | 5 => state15_755 | 6 => state15_756 | _ => state15_757

def stree15LRRLLRR (i : Nat) : State := if i < 7 then stree15LRRLLRRL i else stree15LRRLLRRR (i - 7)

def stree15LRRLLR (i : Nat) : State := if i < 14 then stree15LRRLLRL i else stree15LRRLLRR (i - 14)

def stree15LRRLL (i : Nat) : State := if i < 29 then stree15LRRLLL i else stree15LRRLLR (i - 29)

def stree15LRRLRLLL (i : Nat) : State := match i with | 0 => state15_758 | 1 => state15_759 | 2 => state15_760 | 3 => state15_761 | 4 => state15_762 | 5 => state15_763 | _ => state15_764

def stree15LRRLRLLR (i : Nat) : State := match i with | 0 => state15_765 | 1 => state15_766 | 2 => state15_767 | 3 => state15_768 | 4 => state15_769 | 5 => state15_770 | _ => state15_771

def stree15LRRLRLL (i : Nat) : State := if i < 7 then stree15LRRLRLLL i else stree15LRRLRLLR (i - 7)

def stree15LRRLRLRL (i : Nat) : State := match i with | 0 => state15_772 | 1 => state15_773 | 2 => state15_774 | 3 => state15_775 | 4 => state15_776 | 5 => state15_777 | _ => state15_778

def stree15LRRLRLRR (i : Nat) : State := match i with | 0 => state15_779 | 1 => state15_780 | 2 => state15_781 | 3 => state15_782 | 4 => state15_783 | 5 => state15_784 | 6 => state15_785 | _ => state15_786

def stree15LRRLRLR (i : Nat) : State := if i < 7 then stree15LRRLRLRL i else stree15LRRLRLRR (i - 7)

def stree15LRRLRL (i : Nat) : State := if i < 14 then stree15LRRLRLL i else stree15LRRLRLR (i - 14)

def stree15LRRLRRLL (i : Nat) : State := match i with | 0 => state15_787 | 1 => state15_788 | 2 => state15_789 | 3 => state15_790 | 4 => state15_791 | 5 => state15_792 | _ => state15_793

def stree15LRRLRRLR (i : Nat) : State := match i with | 0 => state15_794 | 1 => state15_795 | 2 => state15_796 | 3 => state15_797 | 4 => state15_798 | 5 => state15_799 | 6 => state15_800 | _ => state15_801

def stree15LRRLRRL (i : Nat) : State := if i < 7 then stree15LRRLRRLL i else stree15LRRLRRLR (i - 7)

def stree15LRRLRRRL (i : Nat) : State := match i with | 0 => state15_802 | 1 => state15_803 | 2 => state15_804 | 3 => state15_805 | 4 => state15_806 | 5 => state15_807 | _ => state15_808

def stree15LRRLRRRR (i : Nat) : State := match i with | 0 => state15_809 | 1 => state15_810 | 2 => state15_811 | 3 => state15_812 | 4 => state15_813 | 5 => state15_814 | 6 => state15_815 | _ => state15_816

def stree15LRRLRRR (i : Nat) : State := if i < 7 then stree15LRRLRRRL i else stree15LRRLRRRR (i - 7)

def stree15LRRLRR (i : Nat) : State := if i < 15 then stree15LRRLRRL i else stree15LRRLRRR (i - 15)

def stree15LRRLR (i : Nat) : State := if i < 29 then stree15LRRLRL i else stree15LRRLRR (i - 29)

def stree15LRRL (i : Nat) : State := if i < 58 then stree15LRRLL i else stree15LRRLR (i - 58)

def stree15LRRRLLLL (i : Nat) : State := match i with | 0 => state15_817 | 1 => state15_818 | 2 => state15_819 | 3 => state15_820 | 4 => state15_821 | 5 => state15_822 | _ => state15_823

def stree15LRRRLLLR (i : Nat) : State := match i with | 0 => state15_824 | 1 => state15_825 | 2 => state15_826 | 3 => state15_827 | 4 => state15_828 | 5 => state15_829 | _ => state15_830

def stree15LRRRLLL (i : Nat) : State := if i < 7 then stree15LRRRLLLL i else stree15LRRRLLLR (i - 7)

def stree15LRRRLLRL (i : Nat) : State := match i with | 0 => state15_831 | 1 => state15_832 | 2 => state15_833 | 3 => state15_834 | 4 => state15_835 | 5 => state15_836 | _ => state15_837

def stree15LRRRLLRR (i : Nat) : State := match i with | 0 => state15_838 | 1 => state15_839 | 2 => state15_840 | 3 => state15_841 | 4 => state15_842 | 5 => state15_843 | 6 => state15_844 | _ => state15_845

def stree15LRRRLLR (i : Nat) : State := if i < 7 then stree15LRRRLLRL i else stree15LRRRLLRR (i - 7)

def stree15LRRRLL (i : Nat) : State := if i < 14 then stree15LRRRLLL i else stree15LRRRLLR (i - 14)

def stree15LRRRLRLL (i : Nat) : State := match i with | 0 => state15_846 | 1 => state15_847 | 2 => state15_848 | 3 => state15_849 | 4 => state15_850 | 5 => state15_851 | _ => state15_852

def stree15LRRRLRLR (i : Nat) : State := match i with | 0 => state15_853 | 1 => state15_854 | 2 => state15_855 | 3 => state15_856 | 4 => state15_857 | 5 => state15_858 | _ => state15_859

def stree15LRRRLRL (i : Nat) : State := if i < 7 then stree15LRRRLRLL i else stree15LRRRLRLR (i - 7)

def stree15LRRRLRRL (i : Nat) : State := match i with | 0 => state15_860 | 1 => state15_861 | 2 => state15_862 | 3 => state15_863 | 4 => state15_864 | 5 => state15_865 | _ => state15_866

def stree15LRRRLRRR (i : Nat) : State := match i with | 0 => state15_867 | 1 => state15_868 | 2 => state15_869 | 3 => state15_870 | 4 => state15_871 | 5 => state15_872 | 6 => state15_873 | _ => state15_874

def stree15LRRRLRR (i : Nat) : State := if i < 7 then stree15LRRRLRRL i else stree15LRRRLRRR (i - 7)

def stree15LRRRLR (i : Nat) : State := if i < 14 then stree15LRRRLRL i else stree15LRRRLRR (i - 14)

def stree15LRRRL (i : Nat) : State := if i < 29 then stree15LRRRLL i else stree15LRRRLR (i - 29)

def stree15LRRRRLLL (i : Nat) : State := match i with | 0 => state15_875 | 1 => state15_876 | 2 => state15_877 | 3 => state15_878 | 4 => state15_879 | 5 => state15_880 | _ => state15_881

def stree15LRRRRLLR (i : Nat) : State := match i with | 0 => state15_882 | 1 => state15_883 | 2 => state15_884 | 3 => state15_885 | 4 => state15_886 | 5 => state15_887 | _ => state15_888

def stree15LRRRRLL (i : Nat) : State := if i < 7 then stree15LRRRRLLL i else stree15LRRRRLLR (i - 7)

def stree15LRRRRLRL (i : Nat) : State := match i with | 0 => state15_889 | 1 => state15_890 | 2 => state15_891 | 3 => state15_892 | 4 => state15_893 | 5 => state15_894 | _ => state15_895

def stree15LRRRRLRR (i : Nat) : State := match i with | 0 => state15_896 | 1 => state15_897 | 2 => state15_898 | 3 => state15_899 | 4 => state15_900 | 5 => state15_901 | 6 => state15_902 | _ => state15_903

def stree15LRRRRLR (i : Nat) : State := if i < 7 then stree15LRRRRLRL i else stree15LRRRRLRR (i - 7)

def stree15LRRRRL (i : Nat) : State := if i < 14 then stree15LRRRRLL i else stree15LRRRRLR (i - 14)

def stree15LRRRRRLL (i : Nat) : State := match i with | 0 => state15_904 | 1 => state15_905 | 2 => state15_906 | 3 => state15_907 | 4 => state15_908 | 5 => state15_909 | _ => state15_910

def stree15LRRRRRLR (i : Nat) : State := match i with | 0 => state15_911 | 1 => state15_912 | 2 => state15_913 | 3 => state15_914 | 4 => state15_915 | 5 => state15_916 | 6 => state15_917 | _ => state15_918

def stree15LRRRRRL (i : Nat) : State := if i < 7 then stree15LRRRRRLL i else stree15LRRRRRLR (i - 7)

def stree15LRRRRRRL (i : Nat) : State := match i with | 0 => state15_919 | 1 => state15_920 | 2 => state15_921 | 3 => state15_922 | 4 => state15_923 | 5 => state15_924 | _ => state15_925

def stree15LRRRRRRR (i : Nat) : State := match i with | 0 => state15_926 | 1 => state15_927 | 2 => state15_928 | 3 => state15_929 | 4 => state15_930 | 5 => state15_931 | 6 => state15_932 | _ => state15_933

def stree15LRRRRRR (i : Nat) : State := if i < 7 then stree15LRRRRRRL i else stree15LRRRRRRR (i - 7)

def stree15LRRRRR (i : Nat) : State := if i < 15 then stree15LRRRRRL i else stree15LRRRRRR (i - 15)

def stree15LRRRR (i : Nat) : State := if i < 29 then stree15LRRRRL i else stree15LRRRRR (i - 29)

def stree15LRRR (i : Nat) : State := if i < 58 then stree15LRRRL i else stree15LRRRR (i - 58)

def stree15LRR (i : Nat) : State := if i < 117 then stree15LRRL i else stree15LRRR (i - 117)

def stree15LR (i : Nat) : State := if i < 233 then stree15LRL i else stree15LRR (i - 233)

def stree15L (i : Nat) : State := if i < 467 then stree15LL i else stree15LR (i - 467)

def stree15RLLLLLLL (i : Nat) : State := match i with | 0 => state15_934 | 1 => state15_935 | 2 => state15_936 | 3 => state15_937 | 4 => state15_938 | 5 => state15_939 | _ => state15_940

def stree15RLLLLLLR (i : Nat) : State := match i with | 0 => state15_941 | 1 => state15_942 | 2 => state15_943 | 3 => state15_944 | 4 => state15_945 | 5 => state15_946 | _ => state15_947

def stree15RLLLLLL (i : Nat) : State := if i < 7 then stree15RLLLLLLL i else stree15RLLLLLLR (i - 7)

def stree15RLLLLLRL (i : Nat) : State := match i with | 0 => state15_948 | 1 => state15_949 | 2 => state15_950 | 3 => state15_951 | 4 => state15_952 | 5 => state15_953 | _ => state15_954

def stree15RLLLLLRR (i : Nat) : State := match i with | 0 => state15_955 | 1 => state15_956 | 2 => state15_957 | 3 => state15_958 | 4 => state15_959 | 5 => state15_960 | 6 => state15_961 | _ => state15_962

def stree15RLLLLLR (i : Nat) : State := if i < 7 then stree15RLLLLLRL i else stree15RLLLLLRR (i - 7)

def stree15RLLLLL (i : Nat) : State := if i < 14 then stree15RLLLLLL i else stree15RLLLLLR (i - 14)

def stree15RLLLLRLL (i : Nat) : State := match i with | 0 => state15_963 | 1 => state15_964 | 2 => state15_965 | 3 => state15_966 | 4 => state15_967 | 5 => state15_968 | _ => state15_969

def stree15RLLLLRLR (i : Nat) : State := match i with | 0 => state15_970 | 1 => state15_971 | 2 => state15_972 | 3 => state15_973 | 4 => state15_974 | 5 => state15_975 | _ => state15_976

def stree15RLLLLRL (i : Nat) : State := if i < 7 then stree15RLLLLRLL i else stree15RLLLLRLR (i - 7)

def stree15RLLLLRRL (i : Nat) : State := match i with | 0 => state15_977 | 1 => state15_978 | 2 => state15_979 | 3 => state15_980 | 4 => state15_981 | 5 => state15_982 | _ => state15_983

def stree15RLLLLRRR (i : Nat) : State := match i with | 0 => state15_984 | 1 => state15_985 | 2 => state15_986 | 3 => state15_987 | 4 => state15_988 | 5 => state15_989 | 6 => state15_990 | _ => state15_991

def stree15RLLLLRR (i : Nat) : State := if i < 7 then stree15RLLLLRRL i else stree15RLLLLRRR (i - 7)

def stree15RLLLLR (i : Nat) : State := if i < 14 then stree15RLLLLRL i else stree15RLLLLRR (i - 14)

def stree15RLLLL (i : Nat) : State := if i < 29 then stree15RLLLLL i else stree15RLLLLR (i - 29)

def stree15RLLLRLLL (i : Nat) : State := match i with | 0 => state15_992 | 1 => state15_993 | 2 => state15_994 | 3 => state15_995 | 4 => state15_996 | 5 => state15_997 | _ => state15_998

def stree15RLLLRLLR (i : Nat) : State := match i with | 0 => state15_999 | 1 => state15_1000 | 2 => state15_1001 | 3 => state15_1002 | 4 => state15_1003 | 5 => state15_1004 | _ => state15_1005

def stree15RLLLRLL (i : Nat) : State := if i < 7 then stree15RLLLRLLL i else stree15RLLLRLLR (i - 7)

def stree15RLLLRLRL (i : Nat) : State := match i with | 0 => state15_1006 | 1 => state15_1007 | 2 => state15_1008 | 3 => state15_1009 | 4 => state15_1010 | 5 => state15_1011 | _ => state15_1012

def stree15RLLLRLRR (i : Nat) : State := match i with | 0 => state15_1013 | 1 => state15_1014 | 2 => state15_1015 | 3 => state15_1016 | 4 => state15_1017 | 5 => state15_1018 | 6 => state15_1019 | _ => state15_1020

def stree15RLLLRLR (i : Nat) : State := if i < 7 then stree15RLLLRLRL i else stree15RLLLRLRR (i - 7)

def stree15RLLLRL (i : Nat) : State := if i < 14 then stree15RLLLRLL i else stree15RLLLRLR (i - 14)

def stree15RLLLRRLL (i : Nat) : State := match i with | 0 => state15_1021 | 1 => state15_1022 | 2 => state15_1023 | 3 => state15_1024 | 4 => state15_1025 | 5 => state15_1026 | _ => state15_1027

def stree15RLLLRRLR (i : Nat) : State := match i with | 0 => state15_1028 | 1 => state15_1029 | 2 => state15_1030 | 3 => state15_1031 | 4 => state15_1032 | 5 => state15_1033 | _ => state15_1034

def stree15RLLLRRL (i : Nat) : State := if i < 7 then stree15RLLLRRLL i else stree15RLLLRRLR (i - 7)

def stree15RLLLRRRL (i : Nat) : State := match i with | 0 => state15_1035 | 1 => state15_1036 | 2 => state15_1037 | 3 => state15_1038 | 4 => state15_1039 | 5 => state15_1040 | _ => state15_1041

def stree15RLLLRRRR (i : Nat) : State := match i with | 0 => state15_1042 | 1 => state15_1043 | 2 => state15_1044 | 3 => state15_1045 | 4 => state15_1046 | 5 => state15_1047 | 6 => state15_1048 | _ => state15_1049

def stree15RLLLRRR (i : Nat) : State := if i < 7 then stree15RLLLRRRL i else stree15RLLLRRRR (i - 7)

def stree15RLLLRR (i : Nat) : State := if i < 14 then stree15RLLLRRL i else stree15RLLLRRR (i - 14)

def stree15RLLLR (i : Nat) : State := if i < 29 then stree15RLLLRL i else stree15RLLLRR (i - 29)

def stree15RLLL (i : Nat) : State := if i < 58 then stree15RLLLL i else stree15RLLLR (i - 58)

def stree15RLLRLLLL (i : Nat) : State := match i with | 0 => state15_1050 | 1 => state15_1051 | 2 => state15_1052 | 3 => state15_1053 | 4 => state15_1054 | 5 => state15_1055 | _ => state15_1056

def stree15RLLRLLLR (i : Nat) : State := match i with | 0 => state15_1057 | 1 => state15_1058 | 2 => state15_1059 | 3 => state15_1060 | 4 => state15_1061 | 5 => state15_1062 | _ => state15_1063

def stree15RLLRLLL (i : Nat) : State := if i < 7 then stree15RLLRLLLL i else stree15RLLRLLLR (i - 7)

def stree15RLLRLLRL (i : Nat) : State := match i with | 0 => state15_1064 | 1 => state15_1065 | 2 => state15_1066 | 3 => state15_1067 | 4 => state15_1068 | 5 => state15_1069 | _ => state15_1070

def stree15RLLRLLRR (i : Nat) : State := match i with | 0 => state15_1071 | 1 => state15_1072 | 2 => state15_1073 | 3 => state15_1074 | 4 => state15_1075 | 5 => state15_1076 | 6 => state15_1077 | _ => state15_1078

def stree15RLLRLLR (i : Nat) : State := if i < 7 then stree15RLLRLLRL i else stree15RLLRLLRR (i - 7)

def stree15RLLRLL (i : Nat) : State := if i < 14 then stree15RLLRLLL i else stree15RLLRLLR (i - 14)

def stree15RLLRLRLL (i : Nat) : State := match i with | 0 => state15_1079 | 1 => state15_1080 | 2 => state15_1081 | 3 => state15_1082 | 4 => state15_1083 | 5 => state15_1084 | _ => state15_1085

def stree15RLLRLRLR (i : Nat) : State := match i with | 0 => state15_1086 | 1 => state15_1087 | 2 => state15_1088 | 3 => state15_1089 | 4 => state15_1090 | 5 => state15_1091 | _ => state15_1092

def stree15RLLRLRL (i : Nat) : State := if i < 7 then stree15RLLRLRLL i else stree15RLLRLRLR (i - 7)

def stree15RLLRLRRL (i : Nat) : State := match i with | 0 => state15_1093 | 1 => state15_1094 | 2 => state15_1095 | 3 => state15_1096 | 4 => state15_1097 | 5 => state15_1098 | _ => state15_1099

def stree15RLLRLRRR (i : Nat) : State := match i with | 0 => state15_1100 | 1 => state15_1101 | 2 => state15_1102 | 3 => state15_1103 | 4 => state15_1104 | 5 => state15_1105 | 6 => state15_1106 | _ => state15_1107

def stree15RLLRLRR (i : Nat) : State := if i < 7 then stree15RLLRLRRL i else stree15RLLRLRRR (i - 7)

def stree15RLLRLR (i : Nat) : State := if i < 14 then stree15RLLRLRL i else stree15RLLRLRR (i - 14)

def stree15RLLRL (i : Nat) : State := if i < 29 then stree15RLLRLL i else stree15RLLRLR (i - 29)

def stree15RLLRRLLL (i : Nat) : State := match i with | 0 => state15_1108 | 1 => state15_1109 | 2 => state15_1110 | 3 => state15_1111 | 4 => state15_1112 | 5 => state15_1113 | _ => state15_1114

def stree15RLLRRLLR (i : Nat) : State := match i with | 0 => state15_1115 | 1 => state15_1116 | 2 => state15_1117 | 3 => state15_1118 | 4 => state15_1119 | 5 => state15_1120 | _ => state15_1121

def stree15RLLRRLL (i : Nat) : State := if i < 7 then stree15RLLRRLLL i else stree15RLLRRLLR (i - 7)

def stree15RLLRRLRL (i : Nat) : State := match i with | 0 => state15_1122 | 1 => state15_1123 | 2 => state15_1124 | 3 => state15_1125 | 4 => state15_1126 | 5 => state15_1127 | _ => state15_1128

def stree15RLLRRLRR (i : Nat) : State := match i with | 0 => state15_1129 | 1 => state15_1130 | 2 => state15_1131 | 3 => state15_1132 | 4 => state15_1133 | 5 => state15_1134 | 6 => state15_1135 | _ => state15_1136

def stree15RLLRRLR (i : Nat) : State := if i < 7 then stree15RLLRRLRL i else stree15RLLRRLRR (i - 7)

def stree15RLLRRL (i : Nat) : State := if i < 14 then stree15RLLRRLL i else stree15RLLRRLR (i - 14)

def stree15RLLRRRLL (i : Nat) : State := match i with | 0 => state15_1137 | 1 => state15_1138 | 2 => state15_1139 | 3 => state15_1140 | 4 => state15_1141 | 5 => state15_1142 | _ => state15_1143

def stree15RLLRRRLR (i : Nat) : State := match i with | 0 => state15_1144 | 1 => state15_1145 | 2 => state15_1146 | 3 => state15_1147 | 4 => state15_1148 | 5 => state15_1149 | 6 => state15_1150 | _ => state15_1151

def stree15RLLRRRL (i : Nat) : State := if i < 7 then stree15RLLRRRLL i else stree15RLLRRRLR (i - 7)

def stree15RLLRRRRL (i : Nat) : State := match i with | 0 => state15_1152 | 1 => state15_1153 | 2 => state15_1154 | 3 => state15_1155 | 4 => state15_1156 | 5 => state15_1157 | _ => state15_1158

def stree15RLLRRRRR (i : Nat) : State := match i with | 0 => state15_1159 | 1 => state15_1160 | 2 => state15_1161 | 3 => state15_1162 | 4 => state15_1163 | 5 => state15_1164 | 6 => state15_1165 | _ => state15_1166

def stree15RLLRRRR (i : Nat) : State := if i < 7 then stree15RLLRRRRL i else stree15RLLRRRRR (i - 7)

def stree15RLLRRR (i : Nat) : State := if i < 15 then stree15RLLRRRL i else stree15RLLRRRR (i - 15)

def stree15RLLRR (i : Nat) : State := if i < 29 then stree15RLLRRL i else stree15RLLRRR (i - 29)

def stree15RLLR (i : Nat) : State := if i < 58 then stree15RLLRL i else stree15RLLRR (i - 58)

def stree15RLL (i : Nat) : State := if i < 116 then stree15RLLL i else stree15RLLR (i - 116)

def stree15RLRLLLLL (i : Nat) : State := match i with | 0 => state15_1167 | 1 => state15_1168 | 2 => state15_1169 | 3 => state15_1170 | 4 => state15_1171 | 5 => state15_1172 | _ => state15_1173

def stree15RLRLLLLR (i : Nat) : State := match i with | 0 => state15_1174 | 1 => state15_1175 | 2 => state15_1176 | 3 => state15_1177 | 4 => state15_1178 | 5 => state15_1179 | _ => state15_1180

def stree15RLRLLLL (i : Nat) : State := if i < 7 then stree15RLRLLLLL i else stree15RLRLLLLR (i - 7)

def stree15RLRLLLRL (i : Nat) : State := match i with | 0 => state15_1181 | 1 => state15_1182 | 2 => state15_1183 | 3 => state15_1184 | 4 => state15_1185 | 5 => state15_1186 | _ => state15_1187

def stree15RLRLLLRR (i : Nat) : State := match i with | 0 => state15_1188 | 1 => state15_1189 | 2 => state15_1190 | 3 => state15_1191 | 4 => state15_1192 | 5 => state15_1193 | 6 => state15_1194 | _ => state15_1195

def stree15RLRLLLR (i : Nat) : State := if i < 7 then stree15RLRLLLRL i else stree15RLRLLLRR (i - 7)

def stree15RLRLLL (i : Nat) : State := if i < 14 then stree15RLRLLLL i else stree15RLRLLLR (i - 14)

def stree15RLRLLRLL (i : Nat) : State := match i with | 0 => state15_1196 | 1 => state15_1197 | 2 => state15_1198 | 3 => state15_1199 | 4 => state15_1200 | 5 => state15_1201 | _ => state15_1202

def stree15RLRLLRLR (i : Nat) : State := match i with | 0 => state15_1203 | 1 => state15_1204 | 2 => state15_1205 | 3 => state15_1206 | 4 => state15_1207 | 5 => state15_1208 | _ => state15_1209

def stree15RLRLLRL (i : Nat) : State := if i < 7 then stree15RLRLLRLL i else stree15RLRLLRLR (i - 7)

def stree15RLRLLRRL (i : Nat) : State := match i with | 0 => state15_1210 | 1 => state15_1211 | 2 => state15_1212 | 3 => state15_1213 | 4 => state15_1214 | 5 => state15_1215 | _ => state15_1216

def stree15RLRLLRRR (i : Nat) : State := match i with | 0 => state15_1217 | 1 => state15_1218 | 2 => state15_1219 | 3 => state15_1220 | 4 => state15_1221 | 5 => state15_1222 | 6 => state15_1223 | _ => state15_1224

def stree15RLRLLRR (i : Nat) : State := if i < 7 then stree15RLRLLRRL i else stree15RLRLLRRR (i - 7)

def stree15RLRLLR (i : Nat) : State := if i < 14 then stree15RLRLLRL i else stree15RLRLLRR (i - 14)

def stree15RLRLL (i : Nat) : State := if i < 29 then stree15RLRLLL i else stree15RLRLLR (i - 29)

def stree15RLRLRLLL (i : Nat) : State := match i with | 0 => state15_1225 | 1 => state15_1226 | 2 => state15_1227 | 3 => state15_1228 | 4 => state15_1229 | 5 => state15_1230 | _ => state15_1231

def stree15RLRLRLLR (i : Nat) : State := match i with | 0 => state15_1232 | 1 => state15_1233 | 2 => state15_1234 | 3 => state15_1235 | 4 => state15_1236 | 5 => state15_1237 | _ => state15_1238

def stree15RLRLRLL (i : Nat) : State := if i < 7 then stree15RLRLRLLL i else stree15RLRLRLLR (i - 7)

def stree15RLRLRLRL (i : Nat) : State := match i with | 0 => state15_1239 | 1 => state15_1240 | 2 => state15_1241 | 3 => state15_1242 | 4 => state15_1243 | 5 => state15_1244 | _ => state15_1245

def stree15RLRLRLRR (i : Nat) : State := match i with | 0 => state15_1246 | 1 => state15_1247 | 2 => state15_1248 | 3 => state15_1249 | 4 => state15_1250 | 5 => state15_1251 | 6 => state15_1252 | _ => state15_1253

def stree15RLRLRLR (i : Nat) : State := if i < 7 then stree15RLRLRLRL i else stree15RLRLRLRR (i - 7)

def stree15RLRLRL (i : Nat) : State := if i < 14 then stree15RLRLRLL i else stree15RLRLRLR (i - 14)

def stree15RLRLRRLL (i : Nat) : State := match i with | 0 => state15_1254 | 1 => state15_1255 | 2 => state15_1256 | 3 => state15_1257 | 4 => state15_1258 | 5 => state15_1259 | _ => state15_1260

def stree15RLRLRRLR (i : Nat) : State := match i with | 0 => state15_1261 | 1 => state15_1262 | 2 => state15_1263 | 3 => state15_1264 | 4 => state15_1265 | 5 => state15_1266 | 6 => state15_1267 | _ => state15_1268

def stree15RLRLRRL (i : Nat) : State := if i < 7 then stree15RLRLRRLL i else stree15RLRLRRLR (i - 7)

def stree15RLRLRRRL (i : Nat) : State := match i with | 0 => state15_1269 | 1 => state15_1270 | 2 => state15_1271 | 3 => state15_1272 | 4 => state15_1273 | 5 => state15_1274 | _ => state15_1275

def stree15RLRLRRRR (i : Nat) : State := match i with | 0 => state15_1276 | 1 => state15_1277 | 2 => state15_1278 | 3 => state15_1279 | 4 => state15_1280 | 5 => state15_1281 | 6 => state15_1282 | _ => state15_1283

def stree15RLRLRRR (i : Nat) : State := if i < 7 then stree15RLRLRRRL i else stree15RLRLRRRR (i - 7)

def stree15RLRLRR (i : Nat) : State := if i < 15 then stree15RLRLRRL i else stree15RLRLRRR (i - 15)

def stree15RLRLR (i : Nat) : State := if i < 29 then stree15RLRLRL i else stree15RLRLRR (i - 29)

def stree15RLRL (i : Nat) : State := if i < 58 then stree15RLRLL i else stree15RLRLR (i - 58)

def stree15RLRRLLLL (i : Nat) : State := match i with | 0 => state15_1284 | 1 => state15_1285 | 2 => state15_1286 | 3 => state15_1287 | 4 => state15_1288 | 5 => state15_1289 | _ => state15_1290

def stree15RLRRLLLR (i : Nat) : State := match i with | 0 => state15_1291 | 1 => state15_1292 | 2 => state15_1293 | 3 => state15_1294 | 4 => state15_1295 | 5 => state15_1296 | _ => state15_1297

def stree15RLRRLLL (i : Nat) : State := if i < 7 then stree15RLRRLLLL i else stree15RLRRLLLR (i - 7)

def stree15RLRRLLRL (i : Nat) : State := match i with | 0 => state15_1298 | 1 => state15_1299 | 2 => state15_1300 | 3 => state15_1301 | 4 => state15_1302 | 5 => state15_1303 | _ => state15_1304

def stree15RLRRLLRR (i : Nat) : State := match i with | 0 => state15_1305 | 1 => state15_1306 | 2 => state15_1307 | 3 => state15_1308 | 4 => state15_1309 | 5 => state15_1310 | 6 => state15_1311 | _ => state15_1312

def stree15RLRRLLR (i : Nat) : State := if i < 7 then stree15RLRRLLRL i else stree15RLRRLLRR (i - 7)

def stree15RLRRLL (i : Nat) : State := if i < 14 then stree15RLRRLLL i else stree15RLRRLLR (i - 14)

def stree15RLRRLRLL (i : Nat) : State := match i with | 0 => state15_1313 | 1 => state15_1314 | 2 => state15_1315 | 3 => state15_1316 | 4 => state15_1317 | 5 => state15_1318 | _ => state15_1319

def stree15RLRRLRLR (i : Nat) : State := match i with | 0 => state15_1320 | 1 => state15_1321 | 2 => state15_1322 | 3 => state15_1323 | 4 => state15_1324 | 5 => state15_1325 | _ => state15_1326

def stree15RLRRLRL (i : Nat) : State := if i < 7 then stree15RLRRLRLL i else stree15RLRRLRLR (i - 7)

def stree15RLRRLRRL (i : Nat) : State := match i with | 0 => state15_1327 | 1 => state15_1328 | 2 => state15_1329 | 3 => state15_1330 | 4 => state15_1331 | 5 => state15_1332 | _ => state15_1333

def stree15RLRRLRRR (i : Nat) : State := match i with | 0 => state15_1334 | 1 => state15_1335 | 2 => state15_1336 | 3 => state15_1337 | 4 => state15_1338 | 5 => state15_1339 | 6 => state15_1340 | _ => state15_1341

def stree15RLRRLRR (i : Nat) : State := if i < 7 then stree15RLRRLRRL i else stree15RLRRLRRR (i - 7)

def stree15RLRRLR (i : Nat) : State := if i < 14 then stree15RLRRLRL i else stree15RLRRLRR (i - 14)

def stree15RLRRL (i : Nat) : State := if i < 29 then stree15RLRRLL i else stree15RLRRLR (i - 29)

def stree15RLRRRLLL (i : Nat) : State := match i with | 0 => state15_1342 | 1 => state15_1343 | 2 => state15_1344 | 3 => state15_1345 | 4 => state15_1346 | 5 => state15_1347 | _ => state15_1348

def stree15RLRRRLLR (i : Nat) : State := match i with | 0 => state15_1349 | 1 => state15_1350 | 2 => state15_1351 | 3 => state15_1352 | 4 => state15_1353 | 5 => state15_1354 | _ => state15_1355

def stree15RLRRRLL (i : Nat) : State := if i < 7 then stree15RLRRRLLL i else stree15RLRRRLLR (i - 7)

def stree15RLRRRLRL (i : Nat) : State := match i with | 0 => state15_1356 | 1 => state15_1357 | 2 => state15_1358 | 3 => state15_1359 | 4 => state15_1360 | 5 => state15_1361 | _ => state15_1362

def stree15RLRRRLRR (i : Nat) : State := match i with | 0 => state15_1363 | 1 => state15_1364 | 2 => state15_1365 | 3 => state15_1366 | 4 => state15_1367 | 5 => state15_1368 | 6 => state15_1369 | _ => state15_1370

def stree15RLRRRLR (i : Nat) : State := if i < 7 then stree15RLRRRLRL i else stree15RLRRRLRR (i - 7)

def stree15RLRRRL (i : Nat) : State := if i < 14 then stree15RLRRRLL i else stree15RLRRRLR (i - 14)

def stree15RLRRRRLL (i : Nat) : State := match i with | 0 => state15_1371 | 1 => state15_1372 | 2 => state15_1373 | 3 => state15_1374 | 4 => state15_1375 | 5 => state15_1376 | _ => state15_1377

def stree15RLRRRRLR (i : Nat) : State := match i with | 0 => state15_1378 | 1 => state15_1379 | 2 => state15_1380 | 3 => state15_1381 | 4 => state15_1382 | 5 => state15_1383 | 6 => state15_1384 | _ => state15_1385

def stree15RLRRRRL (i : Nat) : State := if i < 7 then stree15RLRRRRLL i else stree15RLRRRRLR (i - 7)

def stree15RLRRRRRL (i : Nat) : State := match i with | 0 => state15_1386 | 1 => state15_1387 | 2 => state15_1388 | 3 => state15_1389 | 4 => state15_1390 | 5 => state15_1391 | _ => state15_1392

def stree15RLRRRRRR (i : Nat) : State := match i with | 0 => state15_1393 | 1 => state15_1394 | 2 => state15_1395 | 3 => state15_1396 | 4 => state15_1397 | 5 => state15_1398 | 6 => state15_1399 | _ => state15_1400

def stree15RLRRRRR (i : Nat) : State := if i < 7 then stree15RLRRRRRL i else stree15RLRRRRRR (i - 7)

def stree15RLRRRR (i : Nat) : State := if i < 15 then stree15RLRRRRL i else stree15RLRRRRR (i - 15)

def stree15RLRRR (i : Nat) : State := if i < 29 then stree15RLRRRL i else stree15RLRRRR (i - 29)

def stree15RLRR (i : Nat) : State := if i < 58 then stree15RLRRL i else stree15RLRRR (i - 58)

def stree15RLR (i : Nat) : State := if i < 117 then stree15RLRL i else stree15RLRR (i - 117)

def stree15RL (i : Nat) : State := if i < 233 then stree15RLL i else stree15RLR (i - 233)

def stree15RRLLLLLL (i : Nat) : State := match i with | 0 => state15_1401 | 1 => state15_1402 | 2 => state15_1403 | 3 => state15_1404 | 4 => state15_1405 | 5 => state15_1406 | _ => state15_1407

def stree15RRLLLLLR (i : Nat) : State := match i with | 0 => state15_1408 | 1 => state15_1409 | 2 => state15_1410 | 3 => state15_1411 | 4 => state15_1412 | 5 => state15_1413 | _ => state15_1414

def stree15RRLLLLL (i : Nat) : State := if i < 7 then stree15RRLLLLLL i else stree15RRLLLLLR (i - 7)

def stree15RRLLLLRL (i : Nat) : State := match i with | 0 => state15_1415 | 1 => state15_1416 | 2 => state15_1417 | 3 => state15_1418 | 4 => state15_1419 | 5 => state15_1420 | _ => state15_1421

def stree15RRLLLLRR (i : Nat) : State := match i with | 0 => state15_1422 | 1 => state15_1423 | 2 => state15_1424 | 3 => state15_1425 | 4 => state15_1426 | 5 => state15_1427 | 6 => state15_1428 | _ => state15_1429

def stree15RRLLLLR (i : Nat) : State := if i < 7 then stree15RRLLLLRL i else stree15RRLLLLRR (i - 7)

def stree15RRLLLL (i : Nat) : State := if i < 14 then stree15RRLLLLL i else stree15RRLLLLR (i - 14)

def stree15RRLLLRLL (i : Nat) : State := match i with | 0 => state15_1430 | 1 => state15_1431 | 2 => state15_1432 | 3 => state15_1433 | 4 => state15_1434 | 5 => state15_1435 | _ => state15_1436

def stree15RRLLLRLR (i : Nat) : State := match i with | 0 => state15_1437 | 1 => state15_1438 | 2 => state15_1439 | 3 => state15_1440 | 4 => state15_1441 | 5 => state15_1442 | _ => state15_1443

def stree15RRLLLRL (i : Nat) : State := if i < 7 then stree15RRLLLRLL i else stree15RRLLLRLR (i - 7)

def stree15RRLLLRRL (i : Nat) : State := match i with | 0 => state15_1444 | 1 => state15_1445 | 2 => state15_1446 | 3 => state15_1447 | 4 => state15_1448 | 5 => state15_1449 | _ => state15_1450

def stree15RRLLLRRR (i : Nat) : State := match i with | 0 => state15_1451 | 1 => state15_1452 | 2 => state15_1453 | 3 => state15_1454 | 4 => state15_1455 | 5 => state15_1456 | 6 => state15_1457 | _ => state15_1458

def stree15RRLLLRR (i : Nat) : State := if i < 7 then stree15RRLLLRRL i else stree15RRLLLRRR (i - 7)

def stree15RRLLLR (i : Nat) : State := if i < 14 then stree15RRLLLRL i else stree15RRLLLRR (i - 14)

def stree15RRLLL (i : Nat) : State := if i < 29 then stree15RRLLLL i else stree15RRLLLR (i - 29)

def stree15RRLLRLLL (i : Nat) : State := match i with | 0 => state15_1459 | 1 => state15_1460 | 2 => state15_1461 | 3 => state15_1462 | 4 => state15_1463 | 5 => state15_1464 | _ => state15_1465

def stree15RRLLRLLR (i : Nat) : State := match i with | 0 => state15_1466 | 1 => state15_1467 | 2 => state15_1468 | 3 => state15_1469 | 4 => state15_1470 | 5 => state15_1471 | _ => state15_1472

def stree15RRLLRLL (i : Nat) : State := if i < 7 then stree15RRLLRLLL i else stree15RRLLRLLR (i - 7)

def stree15RRLLRLRL (i : Nat) : State := match i with | 0 => state15_1473 | 1 => state15_1474 | 2 => state15_1475 | 3 => state15_1476 | 4 => state15_1477 | 5 => state15_1478 | _ => state15_1479

def stree15RRLLRLRR (i : Nat) : State := match i with | 0 => state15_1480 | 1 => state15_1481 | 2 => state15_1482 | 3 => state15_1483 | 4 => state15_1484 | 5 => state15_1485 | 6 => state15_1486 | _ => state15_1487

def stree15RRLLRLR (i : Nat) : State := if i < 7 then stree15RRLLRLRL i else stree15RRLLRLRR (i - 7)

def stree15RRLLRL (i : Nat) : State := if i < 14 then stree15RRLLRLL i else stree15RRLLRLR (i - 14)

def stree15RRLLRRLL (i : Nat) : State := match i with | 0 => state15_1488 | 1 => state15_1489 | 2 => state15_1490 | 3 => state15_1491 | 4 => state15_1492 | 5 => state15_1493 | _ => state15_1494

def stree15RRLLRRLR (i : Nat) : State := match i with | 0 => state15_1495 | 1 => state15_1496 | 2 => state15_1497 | 3 => state15_1498 | 4 => state15_1499 | 5 => state15_1500 | _ => state15_1501

def stree15RRLLRRL (i : Nat) : State := if i < 7 then stree15RRLLRRLL i else stree15RRLLRRLR (i - 7)

def stree15RRLLRRRL (i : Nat) : State := match i with | 0 => state15_1502 | 1 => state15_1503 | 2 => state15_1504 | 3 => state15_1505 | 4 => state15_1506 | 5 => state15_1507 | _ => state15_1508

def stree15RRLLRRRR (i : Nat) : State := match i with | 0 => state15_1509 | 1 => state15_1510 | 2 => state15_1511 | 3 => state15_1512 | 4 => state15_1513 | 5 => state15_1514 | 6 => state15_1515 | _ => state15_1516

def stree15RRLLRRR (i : Nat) : State := if i < 7 then stree15RRLLRRRL i else stree15RRLLRRRR (i - 7)

def stree15RRLLRR (i : Nat) : State := if i < 14 then stree15RRLLRRL i else stree15RRLLRRR (i - 14)

def stree15RRLLR (i : Nat) : State := if i < 29 then stree15RRLLRL i else stree15RRLLRR (i - 29)

def stree15RRLL (i : Nat) : State := if i < 58 then stree15RRLLL i else stree15RRLLR (i - 58)

def stree15RRLRLLLL (i : Nat) : State := match i with | 0 => state15_1517 | 1 => state15_1518 | 2 => state15_1519 | 3 => state15_1520 | 4 => state15_1521 | 5 => state15_1522 | _ => state15_1523

def stree15RRLRLLLR (i : Nat) : State := match i with | 0 => state15_1524 | 1 => state15_1525 | 2 => state15_1526 | 3 => state15_1527 | 4 => state15_1528 | 5 => state15_1529 | _ => state15_1530

def stree15RRLRLLL (i : Nat) : State := if i < 7 then stree15RRLRLLLL i else stree15RRLRLLLR (i - 7)

def stree15RRLRLLRL (i : Nat) : State := match i with | 0 => state15_1531 | 1 => state15_1532 | 2 => state15_1533 | 3 => state15_1534 | 4 => state15_1535 | 5 => state15_1536 | _ => state15_1537

def stree15RRLRLLRR (i : Nat) : State := match i with | 0 => state15_1538 | 1 => state15_1539 | 2 => state15_1540 | 3 => state15_1541 | 4 => state15_1542 | 5 => state15_1543 | 6 => state15_1544 | _ => state15_1545

def stree15RRLRLLR (i : Nat) : State := if i < 7 then stree15RRLRLLRL i else stree15RRLRLLRR (i - 7)

def stree15RRLRLL (i : Nat) : State := if i < 14 then stree15RRLRLLL i else stree15RRLRLLR (i - 14)

def stree15RRLRLRLL (i : Nat) : State := match i with | 0 => state15_1546 | 1 => state15_1547 | 2 => state15_1548 | 3 => state15_1549 | 4 => state15_1550 | 5 => state15_1551 | _ => state15_1552

def stree15RRLRLRLR (i : Nat) : State := match i with | 0 => state15_1553 | 1 => state15_1554 | 2 => state15_1555 | 3 => state15_1556 | 4 => state15_1557 | 5 => state15_1558 | _ => state15_1559

def stree15RRLRLRL (i : Nat) : State := if i < 7 then stree15RRLRLRLL i else stree15RRLRLRLR (i - 7)

def stree15RRLRLRRL (i : Nat) : State := match i with | 0 => state15_1560 | 1 => state15_1561 | 2 => state15_1562 | 3 => state15_1563 | 4 => state15_1564 | 5 => state15_1565 | _ => state15_1566

def stree15RRLRLRRR (i : Nat) : State := match i with | 0 => state15_1567 | 1 => state15_1568 | 2 => state15_1569 | 3 => state15_1570 | 4 => state15_1571 | 5 => state15_1572 | 6 => state15_1573 | _ => state15_1574

def stree15RRLRLRR (i : Nat) : State := if i < 7 then stree15RRLRLRRL i else stree15RRLRLRRR (i - 7)

def stree15RRLRLR (i : Nat) : State := if i < 14 then stree15RRLRLRL i else stree15RRLRLRR (i - 14)

def stree15RRLRL (i : Nat) : State := if i < 29 then stree15RRLRLL i else stree15RRLRLR (i - 29)

def stree15RRLRRLLL (i : Nat) : State := match i with | 0 => state15_1575 | 1 => state15_1576 | 2 => state15_1577 | 3 => state15_1578 | 4 => state15_1579 | 5 => state15_1580 | _ => state15_1581

def stree15RRLRRLLR (i : Nat) : State := match i with | 0 => state15_1582 | 1 => state15_1583 | 2 => state15_1584 | 3 => state15_1585 | 4 => state15_1586 | 5 => state15_1587 | _ => state15_1588

def stree15RRLRRLL (i : Nat) : State := if i < 7 then stree15RRLRRLLL i else stree15RRLRRLLR (i - 7)

def stree15RRLRRLRL (i : Nat) : State := match i with | 0 => state15_1589 | 1 => state15_1590 | 2 => state15_1591 | 3 => state15_1592 | 4 => state15_1593 | 5 => state15_1594 | _ => state15_1595

def stree15RRLRRLRR (i : Nat) : State := match i with | 0 => state15_1596 | 1 => state15_1597 | 2 => state15_1598 | 3 => state15_1599 | 4 => state15_1600 | 5 => state15_1601 | 6 => state15_1602 | _ => state15_1603

def stree15RRLRRLR (i : Nat) : State := if i < 7 then stree15RRLRRLRL i else stree15RRLRRLRR (i - 7)

def stree15RRLRRL (i : Nat) : State := if i < 14 then stree15RRLRRLL i else stree15RRLRRLR (i - 14)

def stree15RRLRRRLL (i : Nat) : State := match i with | 0 => state15_1604 | 1 => state15_1605 | 2 => state15_1606 | 3 => state15_1607 | 4 => state15_1608 | 5 => state15_1609 | _ => state15_1610

def stree15RRLRRRLR (i : Nat) : State := match i with | 0 => state15_1611 | 1 => state15_1612 | 2 => state15_1613 | 3 => state15_1614 | 4 => state15_1615 | 5 => state15_1616 | 6 => state15_1617 | _ => state15_1618

def stree15RRLRRRL (i : Nat) : State := if i < 7 then stree15RRLRRRLL i else stree15RRLRRRLR (i - 7)

def stree15RRLRRRRL (i : Nat) : State := match i with | 0 => state15_1619 | 1 => state15_1620 | 2 => state15_1621 | 3 => state15_1622 | 4 => state15_1623 | 5 => state15_1624 | _ => state15_1625

def stree15RRLRRRRR (i : Nat) : State := match i with | 0 => state15_1626 | 1 => state15_1627 | 2 => state15_1628 | 3 => state15_1629 | 4 => state15_1630 | 5 => state15_1631 | 6 => state15_1632 | _ => state15_1633

def stree15RRLRRRR (i : Nat) : State := if i < 7 then stree15RRLRRRRL i else stree15RRLRRRRR (i - 7)

def stree15RRLRRR (i : Nat) : State := if i < 15 then stree15RRLRRRL i else stree15RRLRRRR (i - 15)

def stree15RRLRR (i : Nat) : State := if i < 29 then stree15RRLRRL i else stree15RRLRRR (i - 29)

def stree15RRLR (i : Nat) : State := if i < 58 then stree15RRLRL i else stree15RRLRR (i - 58)

def stree15RRL (i : Nat) : State := if i < 116 then stree15RRLL i else stree15RRLR (i - 116)

def stree15RRRLLLLL (i : Nat) : State := match i with | 0 => state15_1634 | 1 => state15_1635 | 2 => state15_1636 | 3 => state15_1637 | 4 => state15_1638 | 5 => state15_1639 | _ => state15_1640

def stree15RRRLLLLR (i : Nat) : State := match i with | 0 => state15_1641 | 1 => state15_1642 | 2 => state15_1643 | 3 => state15_1644 | 4 => state15_1645 | 5 => state15_1646 | _ => state15_1647

def stree15RRRLLLL (i : Nat) : State := if i < 7 then stree15RRRLLLLL i else stree15RRRLLLLR (i - 7)

def stree15RRRLLLRL (i : Nat) : State := match i with | 0 => state15_1648 | 1 => state15_1649 | 2 => state15_1650 | 3 => state15_1651 | 4 => state15_1652 | 5 => state15_1653 | _ => state15_1654

def stree15RRRLLLRR (i : Nat) : State := match i with | 0 => state15_1655 | 1 => state15_1656 | 2 => state15_1657 | 3 => state15_1658 | 4 => state15_1659 | 5 => state15_1660 | 6 => state15_1661 | _ => state15_1662

def stree15RRRLLLR (i : Nat) : State := if i < 7 then stree15RRRLLLRL i else stree15RRRLLLRR (i - 7)

def stree15RRRLLL (i : Nat) : State := if i < 14 then stree15RRRLLLL i else stree15RRRLLLR (i - 14)

def stree15RRRLLRLL (i : Nat) : State := match i with | 0 => state15_1663 | 1 => state15_1664 | 2 => state15_1665 | 3 => state15_1666 | 4 => state15_1667 | 5 => state15_1668 | _ => state15_1669

def stree15RRRLLRLR (i : Nat) : State := match i with | 0 => state15_1670 | 1 => state15_1671 | 2 => state15_1672 | 3 => state15_1673 | 4 => state15_1674 | 5 => state15_1675 | _ => state15_1676

def stree15RRRLLRL (i : Nat) : State := if i < 7 then stree15RRRLLRLL i else stree15RRRLLRLR (i - 7)

def stree15RRRLLRRL (i : Nat) : State := match i with | 0 => state15_1677 | 1 => state15_1678 | 2 => state15_1679 | 3 => state15_1680 | 4 => state15_1681 | 5 => state15_1682 | _ => state15_1683

def stree15RRRLLRRR (i : Nat) : State := match i with | 0 => state15_1684 | 1 => state15_1685 | 2 => state15_1686 | 3 => state15_1687 | 4 => state15_1688 | 5 => state15_1689 | 6 => state15_1690 | _ => state15_1691

def stree15RRRLLRR (i : Nat) : State := if i < 7 then stree15RRRLLRRL i else stree15RRRLLRRR (i - 7)

def stree15RRRLLR (i : Nat) : State := if i < 14 then stree15RRRLLRL i else stree15RRRLLRR (i - 14)

def stree15RRRLL (i : Nat) : State := if i < 29 then stree15RRRLLL i else stree15RRRLLR (i - 29)

def stree15RRRLRLLL (i : Nat) : State := match i with | 0 => state15_1692 | 1 => state15_1693 | 2 => state15_1694 | 3 => state15_1695 | 4 => state15_1696 | 5 => state15_1697 | _ => state15_1698

def stree15RRRLRLLR (i : Nat) : State := match i with | 0 => state15_1699 | 1 => state15_1700 | 2 => state15_1701 | 3 => state15_1702 | 4 => state15_1703 | 5 => state15_1704 | _ => state15_1705

def stree15RRRLRLL (i : Nat) : State := if i < 7 then stree15RRRLRLLL i else stree15RRRLRLLR (i - 7)

def stree15RRRLRLRL (i : Nat) : State := match i with | 0 => state15_1706 | 1 => state15_1707 | 2 => state15_1708 | 3 => state15_1709 | 4 => state15_1710 | 5 => state15_1711 | _ => state15_1712

def stree15RRRLRLRR (i : Nat) : State := match i with | 0 => state15_1713 | 1 => state15_1714 | 2 => state15_1715 | 3 => state15_1716 | 4 => state15_1717 | 5 => state15_1718 | 6 => state15_1719 | _ => state15_1720

def stree15RRRLRLR (i : Nat) : State := if i < 7 then stree15RRRLRLRL i else stree15RRRLRLRR (i - 7)

def stree15RRRLRL (i : Nat) : State := if i < 14 then stree15RRRLRLL i else stree15RRRLRLR (i - 14)

def stree15RRRLRRLL (i : Nat) : State := match i with | 0 => state15_1721 | 1 => state15_1722 | 2 => state15_1723 | 3 => state15_1724 | 4 => state15_1725 | 5 => state15_1726 | _ => state15_1727

def stree15RRRLRRLR (i : Nat) : State := match i with | 0 => state15_1728 | 1 => state15_1729 | 2 => state15_1730 | 3 => state15_1731 | 4 => state15_1732 | 5 => state15_1733 | 6 => state15_1734 | _ => state15_1735

def stree15RRRLRRL (i : Nat) : State := if i < 7 then stree15RRRLRRLL i else stree15RRRLRRLR (i - 7)

def stree15RRRLRRRL (i : Nat) : State := match i with | 0 => state15_1736 | 1 => state15_1737 | 2 => state15_1738 | 3 => state15_1739 | 4 => state15_1740 | 5 => state15_1741 | _ => state15_1742

def stree15RRRLRRRR (i : Nat) : State := match i with | 0 => state15_1743 | 1 => state15_1744 | 2 => state15_1745 | 3 => state15_1746 | 4 => state15_1747 | 5 => state15_1748 | 6 => state15_1749 | _ => state15_1750

def stree15RRRLRRR (i : Nat) : State := if i < 7 then stree15RRRLRRRL i else stree15RRRLRRRR (i - 7)

def stree15RRRLRR (i : Nat) : State := if i < 15 then stree15RRRLRRL i else stree15RRRLRRR (i - 15)

def stree15RRRLR (i : Nat) : State := if i < 29 then stree15RRRLRL i else stree15RRRLRR (i - 29)

def stree15RRRL (i : Nat) : State := if i < 58 then stree15RRRLL i else stree15RRRLR (i - 58)

def stree15RRRRLLLL (i : Nat) : State := match i with | 0 => state15_1751 | 1 => state15_1752 | 2 => state15_1753 | 3 => state15_1754 | 4 => state15_1755 | 5 => state15_1756 | _ => state15_1757

def stree15RRRRLLLR (i : Nat) : State := match i with | 0 => state15_1758 | 1 => state15_1759 | 2 => state15_1760 | 3 => state15_1761 | 4 => state15_1762 | 5 => state15_1763 | _ => state15_1764

def stree15RRRRLLL (i : Nat) : State := if i < 7 then stree15RRRRLLLL i else stree15RRRRLLLR (i - 7)

def stree15RRRRLLRL (i : Nat) : State := match i with | 0 => state15_1765 | 1 => state15_1766 | 2 => state15_1767 | 3 => state15_1768 | 4 => state15_1769 | 5 => state15_1770 | _ => state15_1771

def stree15RRRRLLRR (i : Nat) : State := match i with | 0 => state15_1772 | 1 => state15_1773 | 2 => state15_1774 | 3 => state15_1775 | 4 => state15_1776 | 5 => state15_1777 | 6 => state15_1778 | _ => state15_1779

def stree15RRRRLLR (i : Nat) : State := if i < 7 then stree15RRRRLLRL i else stree15RRRRLLRR (i - 7)

def stree15RRRRLL (i : Nat) : State := if i < 14 then stree15RRRRLLL i else stree15RRRRLLR (i - 14)

def stree15RRRRLRLL (i : Nat) : State := match i with | 0 => state15_1780 | 1 => state15_1781 | 2 => state15_1782 | 3 => state15_1783 | 4 => state15_1784 | 5 => state15_1785 | _ => state15_1786

def stree15RRRRLRLR (i : Nat) : State := match i with | 0 => state15_1787 | 1 => state15_1788 | 2 => state15_1789 | 3 => state15_1790 | 4 => state15_1791 | 5 => state15_1792 | _ => state15_1793

def stree15RRRRLRL (i : Nat) : State := if i < 7 then stree15RRRRLRLL i else stree15RRRRLRLR (i - 7)

def stree15RRRRLRRL (i : Nat) : State := match i with | 0 => state15_1794 | 1 => state15_1795 | 2 => state15_1796 | 3 => state15_1797 | 4 => state15_1798 | 5 => state15_1799 | _ => state15_1800

def stree15RRRRLRRR (i : Nat) : State := match i with | 0 => state15_1801 | 1 => state15_1802 | 2 => state15_1803 | 3 => state15_1804 | 4 => state15_1805 | 5 => state15_1806 | 6 => state15_1807 | _ => state15_1808

def stree15RRRRLRR (i : Nat) : State := if i < 7 then stree15RRRRLRRL i else stree15RRRRLRRR (i - 7)

def stree15RRRRLR (i : Nat) : State := if i < 14 then stree15RRRRLRL i else stree15RRRRLRR (i - 14)

def stree15RRRRL (i : Nat) : State := if i < 29 then stree15RRRRLL i else stree15RRRRLR (i - 29)

def stree15RRRRRLLL (i : Nat) : State := match i with | 0 => state15_1809 | 1 => state15_1810 | 2 => state15_1811 | 3 => state15_1812 | 4 => state15_1813 | 5 => state15_1814 | _ => state15_1815

def stree15RRRRRLLR (i : Nat) : State := match i with | 0 => state15_1816 | 1 => state15_1817 | 2 => state15_1818 | 3 => state15_1819 | 4 => state15_1820 | 5 => state15_1821 | _ => state15_1822

def stree15RRRRRLL (i : Nat) : State := if i < 7 then stree15RRRRRLLL i else stree15RRRRRLLR (i - 7)

def stree15RRRRRLRL (i : Nat) : State := match i with | 0 => state15_1823 | 1 => state15_1824 | 2 => state15_1825 | 3 => state15_1826 | 4 => state15_1827 | 5 => state15_1828 | _ => state15_1829

def stree15RRRRRLRR (i : Nat) : State := match i with | 0 => state15_1830 | 1 => state15_1831 | 2 => state15_1832 | 3 => state15_1833 | 4 => state15_1834 | 5 => state15_1835 | 6 => state15_1836 | _ => state15_1837

def stree15RRRRRLR (i : Nat) : State := if i < 7 then stree15RRRRRLRL i else stree15RRRRRLRR (i - 7)

def stree15RRRRRL (i : Nat) : State := if i < 14 then stree15RRRRRLL i else stree15RRRRRLR (i - 14)

def stree15RRRRRRLL (i : Nat) : State := match i with | 0 => state15_1838 | 1 => state15_1839 | 2 => state15_1840 | 3 => state15_1841 | 4 => state15_1842 | 5 => state15_1843 | _ => state15_1844

def stree15RRRRRRLR (i : Nat) : State := match i with | 0 => state15_1845 | 1 => state15_1846 | 2 => state15_1847 | 3 => state15_1848 | 4 => state15_1849 | 5 => state15_1850 | 6 => state15_1851 | _ => state15_1852

def stree15RRRRRRL (i : Nat) : State := if i < 7 then stree15RRRRRRLL i else stree15RRRRRRLR (i - 7)

def stree15RRRRRRRL (i : Nat) : State := match i with | 0 => state15_1853 | 1 => state15_1854 | 2 => state15_1855 | 3 => state15_1856 | 4 => state15_1857 | 5 => state15_1858 | _ => state15_1859

def stree15RRRRRRRR (i : Nat) : State := match i with | 0 => state15_1860 | 1 => state15_1861 | 2 => state15_1862 | 3 => state15_1863 | 4 => state15_1864 | 5 => state15_1865 | 6 => state15_1866 | _ => state15_1867

def stree15RRRRRRR (i : Nat) : State := if i < 7 then stree15RRRRRRRL i else stree15RRRRRRRR (i - 7)

def stree15RRRRRR (i : Nat) : State := if i < 15 then stree15RRRRRRL i else stree15RRRRRRR (i - 15)

def stree15RRRRR (i : Nat) : State := if i < 29 then stree15RRRRRL i else stree15RRRRRR (i - 29)

def stree15RRRR (i : Nat) : State := if i < 58 then stree15RRRRL i else stree15RRRRR (i - 58)

def stree15RRR (i : Nat) : State := if i < 117 then stree15RRRL i else stree15RRRR (i - 117)

def stree15RR (i : Nat) : State := if i < 233 then stree15RRL i else stree15RRR (i - 233)

def stree15R (i : Nat) : State := if i < 467 then stree15RL i else stree15RR (i - 467)

def stree15 (i : Nat) : State := if i < 934 then stree15L i else stree15R (i - 934)

def ntree15LLLLLLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨3,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | 4 => ![⟨5,by decide⟩,⟨0,by decide⟩,⟨5,by decide⟩] | 5 => ![⟨5,by decide⟩,⟨1,by decide⟩,⟨6,by decide⟩] | _ => ![⟨5,by decide⟩,⟨2,by decide⟩,⟨7,by decide⟩]

def ntree15LLLLLLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨8,by decide⟩,⟨4,by decide⟩,⟨9,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨0,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨1,by decide⟩,⟨11,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨2,by decide⟩,⟨12,by decide⟩] | 4 => ![⟨13,by decide⟩,⟨4,by decide⟩,⟨14,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨16,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨15,by decide⟩,⟨17,by decide⟩,⟨18,by decide⟩] | _ => ![⟨15,by decide⟩,⟨19,by decide⟩,⟨20,by decide⟩]

def ntree15LLLLLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLLLLLLL i else ntree15LLLLLLLR (i - 7)

def ntree15LLLLLLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨21,by decide⟩,⟨22,by decide⟩,⟨23,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨24,by decide⟩] | 2 => ![⟨25,by decide⟩,⟨1,by decide⟩,⟨26,by decide⟩] | 3 => ![⟨5,by decide⟩,⟨27,by decide⟩,⟨28,by decide⟩] | 4 => ![⟨29,by decide⟩,⟨30,by decide⟩,⟨31,by decide⟩] | 5 => ![⟨32,by decide⟩,⟨32,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨33,by decide⟩,⟨0,by decide⟩]

def ntree15LLLLLLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨34,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨35,by decide⟩,⟨35,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨36,by decide⟩] | 3 => ![⟨37,by decide⟩,⟨2,by decide⟩,⟨38,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨39,by decide⟩,⟨40,by decide⟩] | 5 => ![⟨41,by decide⟩,⟨42,by decide⟩,⟨43,by decide⟩] | 6 => ![⟨44,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨45,by decide⟩,⟨0,by decide⟩]

def ntree15LLLLLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLLLLLRL i else ntree15LLLLLLRR (i - 7)

def ntree15LLLLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LLLLLLL i else ntree15LLLLLLR (i - 15)

def ntree15LLLLLRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨46,by decide⟩,⟨46,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨46,by decide⟩,⟨47,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨46,by decide⟩,⟨48,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨49,by decide⟩,⟨50,by decide⟩,⟨4,by decide⟩] | 4 => ![⟨51,by decide⟩,⟨46,by decide⟩,⟨5,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨52,by decide⟩,⟨0,by decide⟩] | _ => ![⟨53,by decide⟩,⟨54,by decide⟩,⟨1,by decide⟩]

def ntree15LLLLLRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨55,by decide⟩,⟨55,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨56,by decide⟩,⟨56,by decide⟩] | 2 => ![⟨5,by decide⟩,⟨56,by decide⟩,⟨57,by decide⟩] | 3 => ![⟨46,by decide⟩,⟨58,by decide⟩,⟨56,by decide⟩] | 4 => ![⟨59,by decide⟩,⟨0,by decide⟩,⟨59,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨60,by decide⟩,⟨60,by decide⟩] | 6 => ![⟨59,by decide⟩,⟨60,by decide⟩,⟨61,by decide⟩] | _ => ![⟨32,by decide⟩,⟨62,by decide⟩,⟨60,by decide⟩]

def ntree15LLLLLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLLLLRLL i else ntree15LLLLLRLR (i - 7)

def ntree15LLLLLRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨63,by decide⟩] | 1 => ![⟨64,by decide⟩,⟨46,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨65,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨66,by decide⟩,⟨67,by decide⟩,⟨15,by decide⟩] | 4 => ![⟨68,by decide⟩,⟨69,by decide⟩,⟨5,by decide⟩] | 5 => ![⟨70,by decide⟩,⟨0,by decide⟩,⟨70,by decide⟩] | _ => ![⟨70,by decide⟩,⟨1,by decide⟩,⟨71,by decide⟩]

def ntree15LLLLLRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨72,by decide⟩,⟨0,by decide⟩,⟨72,by decide⟩] | 1 => ![⟨73,by decide⟩,⟨46,by decide⟩,⟨70,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨74,by decide⟩] | 3 => ![⟨75,by decide⟩,⟨35,by decide⟩,⟨59,by decide⟩] | 4 => ![⟨76,by decide⟩,⟨76,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨76,by decide⟩,⟨77,by decide⟩,⟨1,by decide⟩] | 6 => ![⟨76,by decide⟩,⟨78,by decide⟩,⟨2,by decide⟩] | _ => ![⟨79,by decide⟩,⟨80,by decide⟩,⟨4,by decide⟩]

def ntree15LLLLLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLLLLRRL i else ntree15LLLLLRRR (i - 7)

def ntree15LLLLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LLLLLRL i else ntree15LLLLLRR (i - 15)

def ntree15LLLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15LLLLLL i else ntree15LLLLLR (i - 30)

def ntree15LLLLRLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨81,by decide⟩,⟨76,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨82,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨83,by decide⟩,⟨84,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨85,by decide⟩,⟨0,by decide⟩,⟨85,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨86,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨87,by decide⟩,⟨87,by decide⟩] | _ => ![⟨35,by decide⟩,⟨88,by decide⟩,⟨87,by decide⟩]

def ntree15LLLLRLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨85,by decide⟩,⟨87,by decide⟩,⟨89,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨90,by decide⟩,⟨90,by decide⟩] | 2 => ![⟨76,by decide⟩,⟨91,by decide⟩,⟨90,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨92,by decide⟩,⟨92,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨90,by decide⟩,⟨93,by decide⟩] | 5 => ![⟨94,by decide⟩,⟨94,by decide⟩,⟨95,by decide⟩] | 6 => ![⟨94,by decide⟩,⟨96,by decide⟩,⟨97,by decide⟩] | _ => ![⟨94,by decide⟩,⟨98,by decide⟩,⟨99,by decide⟩]

def ntree15LLLLRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLLLRLLL i else ntree15LLLLRLLR (i - 7)

def ntree15LLLLRLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨100,by decide⟩,⟨101,by decide⟩,⟨102,by decide⟩] | 1 => ![⟨76,by decide⟩,⟨103,by decide⟩,⟨104,by decide⟩] | 2 => ![⟨105,by decide⟩,⟨106,by decide⟩,⟨107,by decide⟩] | 3 => ![⟨46,by decide⟩,⟨108,by decide⟩,⟨109,by decide⟩] | 4 => ![⟨110,by decide⟩,⟨111,by decide⟩,⟨112,by decide⟩] | 5 => ![⟨113,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨114,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LLLLRLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨115,by decide⟩,⟨94,by decide⟩,⟨116,by decide⟩] | 1 => ![⟨117,by decide⟩,⟨76,by decide⟩,⟨118,by decide⟩] | 2 => ![⟨119,by decide⟩,⟨119,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨119,by decide⟩,⟨120,by decide⟩,⟨1,by decide⟩] | 4 => ![⟨121,by decide⟩,⟨121,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨122,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨123,by decide⟩,⟨119,by decide⟩,⟨10,by decide⟩] | _ => ![⟨124,by decide⟩,⟨76,by decide⟩,⟨5,by decide⟩]

def ntree15LLLLRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLLLRLRL i else ntree15LLLLRLRR (i - 7)

def ntree15LLLLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LLLLRLL i else ntree15LLLLRLR (i - 15)

def ntree15LLLLRRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨125,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨126,by decide⟩,⟨127,by decide⟩,⟨15,by decide⟩] | 2 => ![⟨128,by decide⟩,⟨129,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨130,by decide⟩,⟨32,by decide⟩,⟨85,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨131,by decide⟩] | 5 => ![⟨132,by decide⟩,⟨0,by decide⟩,⟨132,by decide⟩] | _ => ![⟨133,by decide⟩,⟨76,by decide⟩,⟨132,by decide⟩]

def ntree15LLLLRRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨134,by decide⟩,⟨0,by decide⟩,⟨134,by decide⟩] | 1 => ![⟨132,by decide⟩,⟨2,by decide⟩,⟨135,by decide⟩] | 2 => ![⟨136,by decide⟩,⟨94,by decide⟩,⟨137,by decide⟩] | 3 => ![⟨138,by decide⟩,⟨46,by decide⟩,⟨139,by decide⟩] | 4 => ![⟨140,by decide⟩,⟨140,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨141,by decide⟩,⟨141,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨142,by decide⟩,⟨141,by decide⟩,⟨5,by decide⟩] | _ => ![⟨0,by decide⟩,⟨143,by decide⟩,⟨0,by decide⟩]

def ntree15LLLLRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLLLRRLL i else ntree15LLLLRRLR (i - 7)

def ntree15LLLLRRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨141,by decide⟩,⟨144,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨145,by decide⟩,⟨146,by decide⟩,⟨147,by decide⟩] | 2 => ![⟨148,by decide⟩,⟨149,by decide⟩,⟨150,by decide⟩] | 3 => ![⟨151,by decide⟩,⟨152,by decide⟩,⟨153,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨154,by decide⟩] | 5 => ![⟨155,by decide⟩,⟨1,by decide⟩,⟨156,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨157,by decide⟩,⟨158,by decide⟩] | _ => ![⟨159,by decide⟩,⟨160,by decide⟩,⟨161,by decide⟩]

def ntree15LLLLRRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨162,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨162,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 5 => ![⟨163,by decide⟩,⟨163,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨164,by decide⟩,⟨0,by decide⟩] | _ => ![⟨163,by decide⟩,⟨165,by decide⟩,⟨1,by decide⟩]

def ntree15LLLLRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 8 then ntree15LLLLRRRL i else ntree15LLLLRRRR (i - 8)

def ntree15LLLLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LLLLRRL i else ntree15LLLLRRR (i - 15)

def ntree15LLLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15LLLLRL i else ntree15LLLLRR (i - 30)

def ntree15LLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 60 then ntree15LLLLL i else ntree15LLLLR (i - 60)

def ntree15LLLRLLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨166,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨167,by decide⟩,⟨167,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨167,by decide⟩,⟨168,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨169,by decide⟩,⟨170,by decide⟩] | 4 => ![⟨163,by decide⟩,⟨171,by decide⟩,⟨170,by decide⟩] | 5 => ![⟨167,by decide⟩,⟨172,by decide⟩,⟨170,by decide⟩] | _ => ![⟨173,by decide⟩,⟨174,by decide⟩,⟨175,by decide⟩]

def ntree15LLLRLLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨176,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨177,by decide⟩,⟨0,by decide⟩,⟨178,by decide⟩] | 3 => ![⟨179,by decide⟩,⟨163,by decide⟩,⟨178,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨180,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨181,by decide⟩,⟨167,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨182,by decide⟩,⟨163,by decide⟩,⟨10,by decide⟩] | _ => ![⟨183,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LLLRLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLLRLLLL i else ntree15LLLRLLLR (i - 7)

def ntree15LLLRLLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨184,by decide⟩,⟨167,by decide⟩,⟨178,by decide⟩] | 1 => ![⟨185,by decide⟩,⟨186,by decide⟩,⟨187,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨180,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨188,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨189,by decide⟩,⟨189,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨189,by decide⟩,⟨190,by decide⟩,⟨1,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LLLRLLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨191,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨192,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨193,by decide⟩,⟨193,by decide⟩,⟨194,by decide⟩] | 4 => ![⟨46,by decide⟩,⟨195,by decide⟩,⟨196,by decide⟩] | 5 => ![⟨193,by decide⟩,⟨197,by decide⟩,⟨198,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨199,by decide⟩] | _ => ![⟨163,by decide⟩,⟨163,by decide⟩,⟨199,by decide⟩]

def ntree15LLLRLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLLRLLRL i else ntree15LLLRLLRR (i - 7)

def ntree15LLLRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LLLRLLL i else ntree15LLLRLLR (i - 15)

def ntree15LLLRLRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨46,by decide⟩,⟨46,by decide⟩,⟨199,by decide⟩] | 1 => ![⟨194,by decide⟩,⟨194,by decide⟩,⟨194,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨196,by decide⟩,⟨196,by decide⟩] | 3 => ![⟨194,by decide⟩,⟨198,by decide⟩,⟨198,by decide⟩] | 4 => ![⟨163,by decide⟩,⟨200,by decide⟩,⟨56,by decide⟩] | 5 => ![⟨201,by decide⟩,⟨46,by decide⟩,⟨202,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LLLRLRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨203,by decide⟩] | 1 => ![⟨46,by decide⟩,⟨46,by decide⟩,⟨203,by decide⟩] | 2 => ![⟨167,by decide⟩,⟨167,by decide⟩,⟨203,by decide⟩] | 3 => ![⟨204,by decide⟩,⟨204,by decide⟩,⟨205,by decide⟩] | 4 => ![⟨205,by decide⟩,⟨205,by decide⟩,⟨205,by decide⟩] | 5 => ![⟨206,by decide⟩,⟨204,by decide⟩,⟨207,by decide⟩] | 6 => ![⟨208,by decide⟩,⟨205,by decide⟩,⟨205,by decide⟩] | _ => ![⟨209,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LLLRLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLLRLRLL i else ntree15LLLRLRLR (i - 7)

def ntree15LLLRLRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨210,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨211,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨212,by decide⟩,⟨213,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨213,by decide⟩,⟨213,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨76,by decide⟩,⟨214,by decide⟩,⟨215,by decide⟩] | 5 => ![⟨216,by decide⟩,⟨216,by decide⟩,⟨217,by decide⟩] | _ => ![⟨216,by decide⟩,⟨218,by decide⟩,⟨219,by decide⟩]

def ntree15LLLRLRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨220,by decide⟩] | 1 => ![⟨167,by decide⟩,⟨167,by decide⟩,⟨220,by decide⟩] | 2 => ![⟨76,by decide⟩,⟨76,by decide⟩,⟨220,by decide⟩] | 3 => ![⟨217,by decide⟩,⟨217,by decide⟩,⟨217,by decide⟩] | 4 => ![⟨217,by decide⟩,⟨221,by decide⟩,⟨217,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨222,by decide⟩,⟨222,by decide⟩] | 6 => ![⟨223,by decide⟩,⟨223,by decide⟩,⟨223,by decide⟩] | _ => ![⟨223,by decide⟩,⟨224,by decide⟩,⟨224,by decide⟩]

def ntree15LLLRLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLLRLRRL i else ntree15LLLRLRRR (i - 7)

def ntree15LLLRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LLLRLRL i else ntree15LLLRLRR (i - 15)

def ntree15LLLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15LLLRLL i else ntree15LLLRLR (i - 30)

def ntree15LLLRRLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨76,by decide⟩,⟨225,by decide⟩,⟨222,by decide⟩] | 1 => ![⟨226,by decide⟩,⟨226,by decide⟩,⟨223,by decide⟩] | 2 => ![⟨226,by decide⟩,⟨227,by decide⟩,⟨224,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨228,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨223,by decide⟩,⟨229,by decide⟩,⟨223,by decide⟩] | 5 => ![⟨230,by decide⟩,⟨230,by decide⟩,⟨223,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LLLRRLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨231,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨231,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨76,by decide⟩,⟨76,by decide⟩,⟨199,by decide⟩] | 3 => ![⟨46,by decide⟩,⟨46,by decide⟩,⟨220,by decide⟩] | 4 => ![⟨94,by decide⟩,⟨94,by decide⟩,⟨232,by decide⟩] | 5 => ![⟨85,by decide⟩,⟨222,by decide⟩,⟨233,by decide⟩] | 6 => ![⟨234,by decide⟩,⟨223,by decide⟩,⟨223,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨235,by decide⟩]

def ntree15LLLRRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLLRRLLL i else ntree15LLLRRLLR (i - 7)

def ntree15LLLRRLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨236,by decide⟩,⟨0,by decide⟩,⟨236,by decide⟩] | 1 => ![⟨236,by decide⟩,⟨1,by decide⟩,⟨237,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨222,by decide⟩,⟨238,by decide⟩] | 3 => ![⟨239,by decide⟩,⟨223,by decide⟩,⟨239,by decide⟩] | 4 => ![⟨239,by decide⟩,⟨224,by decide⟩,⟨240,by decide⟩] | 5 => ![⟨241,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨242,by decide⟩,⟨46,by decide⟩,⟨236,by decide⟩]

def ntree15LLLRRLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨243,by decide⟩,⟨223,by decide⟩,⟨223,by decide⟩] | 2 => ![⟨244,by decide⟩,⟨230,by decide⟩,⟨239,by decide⟩] | 3 => ![⟨245,by decide⟩,⟨245,by decide⟩,⟨246,by decide⟩] | 4 => ![⟨247,by decide⟩,⟨247,by decide⟩,⟨205,by decide⟩] | 5 => ![⟨119,by decide⟩,⟨248,by decide⟩,⟨222,by decide⟩] | 6 => ![⟨249,by decide⟩,⟨249,by decide⟩,⟨223,by decide⟩] | _ => ![⟨249,by decide⟩,⟨250,by decide⟩,⟨224,by decide⟩]

def ntree15LLLRRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLLRRLRL i else ntree15LLLRRLRR (i - 7)

def ntree15LLLRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LLLRRLL i else ntree15LLLRRLR (i - 15)

def ntree15LLLRRRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨223,by decide⟩,⟨251,by decide⟩,⟨223,by decide⟩] | 1 => ![⟨252,by decide⟩,⟨252,by decide⟩,⟨217,by decide⟩] | 2 => ![⟨253,by decide⟩,⟨253,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨254,by decide⟩,⟨119,by decide⟩,⟨236,by decide⟩] | 4 => ![⟨255,by decide⟩,⟨249,by decide⟩,⟨239,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LLLRRRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨256,by decide⟩] | 1 => ![⟨76,by decide⟩,⟨76,by decide⟩,⟨256,by decide⟩] | 2 => ![⟨163,by decide⟩,⟨163,by decide⟩,⟨256,by decide⟩] | 3 => ![⟨257,by decide⟩,⟨257,by decide⟩,⟨258,by decide⟩] | 4 => ![⟨258,by decide⟩,⟨258,by decide⟩,⟨258,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨259,by decide⟩,⟨257,by decide⟩,⟨260,by decide⟩] | _ => ![⟨261,by decide⟩,⟨76,by decide⟩,⟨262,by decide⟩]

def ntree15LLLRRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLLRRRLL i else ntree15LLLRRRLR (i - 7)

def ntree15LLLRRRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨260,by decide⟩,⟨258,by decide⟩,⟨260,by decide⟩] | 1 => ![⟨262,by decide⟩,⟨0,by decide⟩,⟨262,by decide⟩] | 2 => ![⟨263,by decide⟩,⟨163,by decide⟩,⟨132,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨264,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨265,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨266,by decide⟩] | 6 => ![⟨223,by decide⟩,⟨223,by decide⟩,⟨267,by decide⟩] | _ => ![⟨268,by decide⟩,⟨268,by decide⟩,⟨269,by decide⟩]

def ntree15LLLRRRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨270,by decide⟩,⟨270,by decide⟩,⟨258,by decide⟩] | 1 => ![⟨271,by decide⟩,⟨271,by decide⟩,⟨194,by decide⟩] | 2 => ![⟨272,by decide⟩,⟨272,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨273,by decide⟩,⟨273,by decide⟩,⟨223,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨274,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨76,by decide⟩,⟨76,by decide⟩,⟨203,by decide⟩] | _ => ![⟨46,by decide⟩,⟨46,by decide⟩,⟨256,by decide⟩]

def ntree15LLLRRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 8 then ntree15LLLRRRRL i else ntree15LLLRRRRR (i - 8)

def ntree15LLLRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LLLRRRL i else ntree15LLLRRRR (i - 15)

def ntree15LLLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15LLLRRL i else ntree15LLLRRR (i - 30)

def ntree15LLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 60 then ntree15LLLRL i else ntree15LLLRR (i - 60)

def ntree15LLL (i : Nat) : Fin 3 → Fin 1868 := if i < 121 then ntree15LLLL i else ntree15LLLR (i - 121)

def ntree15LLRLLLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨94,by decide⟩,⟨94,by decide⟩,⟨275,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨274,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨236,by decide⟩,⟨60,by decide⟩,⟨276,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨277,by decide⟩] | 4 => ![⟨278,by decide⟩,⟨2,by decide⟩,⟨279,by decide⟩] | 5 => ![⟨5,by decide⟩,⟨280,by decide⟩,⟨281,by decide⟩] | _ => ![⟨282,by decide⟩,⟨283,by decide⟩,⟨284,by decide⟩]

def ntree15LLRLLLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨285,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨286,by decide⟩,⟨163,by decide⟩,⟨5,by decide⟩] | 2 => ![⟨287,by decide⟩,⟨0,by decide⟩,⟨288,by decide⟩] | 3 => ![⟨289,by decide⟩,⟨167,by decide⟩,⟨288,by decide⟩] | 4 => ![⟨290,by decide⟩,⟨167,by decide⟩,⟨5,by decide⟩] | 5 => ![⟨291,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨292,by decide⟩,⟨163,by decide⟩,⟨288,by decide⟩] | _ => ![⟨293,by decide⟩,⟨294,by decide⟩,⟨295,by decide⟩]

def ntree15LLRLLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLRLLLLL i else ntree15LLRLLLLR (i - 7)

def ntree15LLRLLLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨296,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨5,by decide⟩,⟨296,by decide⟩,⟨5,by decide⟩] | 2 => ![⟨297,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨297,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨298,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨163,by decide⟩,⟨299,by decide⟩,⟨2,by decide⟩] | _ => ![⟨0,by decide⟩,⟨300,by decide⟩,⟨0,by decide⟩]

def ntree15LLRLLLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨167,by decide⟩,⟨301,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨302,by decide⟩,⟨303,by decide⟩] | 2 => ![⟨167,by decide⟩,⟨304,by decide⟩,⟨303,by decide⟩] | 3 => ![⟨163,by decide⟩,⟨305,by decide⟩,⟨303,by decide⟩] | 4 => ![⟨306,by decide⟩,⟨307,by decide⟩,⟨308,by decide⟩] | 5 => ![⟨309,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨310,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨311,by decide⟩,⟨189,by decide⟩,⟨5,by decide⟩]

def ntree15LLRLLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLRLLLRL i else ntree15LLRLLLRR (i - 7)

def ntree15LLRLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LLRLLLL i else ntree15LLRLLLR (i - 15)

def ntree15LLRLLRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨312,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨46,by decide⟩,⟨313,by decide⟩,⟨314,by decide⟩] | 2 => ![⟨193,by decide⟩,⟨315,by decide⟩,⟨316,by decide⟩] | 3 => ![⟨194,by decide⟩,⟨317,by decide⟩,⟨194,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨318,by decide⟩,⟨204,by decide⟩,⟨319,by decide⟩]

def ntree15LLRLLRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨320,by decide⟩,⟨46,by decide⟩,⟨321,by decide⟩] | 1 => ![⟨319,by decide⟩,⟨205,by decide⟩,⟨319,by decide⟩] | 2 => ![⟨321,by decide⟩,⟨0,by decide⟩,⟨321,by decide⟩] | 3 => ![⟨322,by decide⟩,⟨167,by decide⟩,⟨70,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨323,by decide⟩,⟨0,by decide⟩]

def ntree15LLRLLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLRLLRLL i else ntree15LLRLLRLR (i - 7)

def ntree15LLRLLRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨324,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨325,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨213,by decide⟩,⟨326,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨327,by decide⟩,⟨76,by decide⟩,⟨328,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨76,by decide⟩,⟨329,by decide⟩,⟨330,by decide⟩] | _ => ![⟨216,by decide⟩,⟨331,by decide⟩,⟨332,by decide⟩]

def ntree15LLRLLRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨167,by decide⟩,⟨333,by decide⟩,⟨90,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨330,by decide⟩,⟨330,by decide⟩] | 2 => ![⟨217,by decide⟩,⟨332,by decide⟩,⟨332,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨334,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨223,by decide⟩,⟨335,by decide⟩,⟨223,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨336,by decide⟩,⟨336,by decide⟩] | 6 => ![⟨223,by decide⟩,⟨337,by decide⟩,⟨337,by decide⟩] | _ => ![⟨46,by decide⟩,⟨338,by decide⟩,⟨336,by decide⟩]

def ntree15LLRLLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLRLLRRL i else ntree15LLRLLRRR (i - 7)

def ntree15LLRLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LLRLLRL i else ntree15LLRLLRR (i - 15)

def ntree15LLRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15LLRLLL i else ntree15LLRLLR (i - 30)

def ntree15LLRLRLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨230,by decide⟩,⟨339,by decide⟩,⟨337,by decide⟩] | 1 => ![⟨340,by decide⟩,⟨223,by decide⟩,⟨223,by decide⟩] | 2 => ![⟨341,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨341,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 4 => ![⟨59,by decide⟩,⟨336,by decide⟩,⟨342,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨343,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨344,by decide⟩]

def ntree15LLRLRLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨345,by decide⟩] | 1 => ![⟨223,by decide⟩,⟨223,by decide⟩,⟨346,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨347,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨348,by decide⟩,⟨257,by decide⟩,⟨349,by decide⟩] | 4 => ![⟨350,by decide⟩,⟨258,by decide⟩,⟨258,by decide⟩] | 5 => ![⟨351,by decide⟩,⟨0,by decide⟩,⟨351,by decide⟩] | 6 => ![⟨352,by decide⟩,⟨76,by decide⟩,⟨351,by decide⟩] | _ => ![⟨353,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LLRLRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLRLRLLL i else ntree15LLRLRLLR (i - 7)

def ntree15LLRLRLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨354,by decide⟩,⟨223,by decide⟩,⟨354,by decide⟩] | 1 => ![⟨355,by decide⟩,⟨226,by decide⟩,⟨354,by decide⟩] | 2 => ![⟨356,by decide⟩,⟨223,by decide⟩,⟨223,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨357,by decide⟩] | 5 => ![⟨351,by decide⟩,⟨2,by decide⟩,⟨358,by decide⟩] | _ => ![⟨5,by decide⟩,⟨336,by decide⟩,⟨359,by decide⟩]

def ntree15LLRLRLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨354,by decide⟩,⟨337,by decide⟩,⟨360,by decide⟩] | 1 => ![⟨361,by decide⟩,⟨141,by decide⟩,⟨351,by decide⟩] | 2 => ![⟨362,by decide⟩,⟨273,by decide⟩,⟨354,by decide⟩] | 3 => ![⟨223,by decide⟩,⟨363,by decide⟩,⟨223,by decide⟩] | 4 => ![⟨141,by decide⟩,⟨364,by decide⟩,⟨336,by decide⟩] | 5 => ![⟨273,by decide⟩,⟨365,by decide⟩,⟨337,by decide⟩] | 6 => ![⟨5,by decide⟩,⟨347,by decide⟩,⟨5,by decide⟩] | _ => ![⟨351,by decide⟩,⟨87,by decide⟩,⟨366,by decide⟩]

def ntree15LLRLRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLRLRLRL i else ntree15LLRLRLRR (i - 7)

def ntree15LLRLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LLRLRLL i else ntree15LLRLRLR (i - 15)

def ntree15LLRLRRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨367,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨367,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨5,by decide⟩,⟨368,by decide⟩,⟨5,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨368,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨369,by decide⟩,⟨10,by decide⟩] | _ => ![⟨0,by decide⟩,⟨369,by decide⟩,⟨0,by decide⟩]

def ntree15LLRLRRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨15,by decide⟩,⟨370,by decide⟩,⟨15,by decide⟩] | 1 => ![⟨5,by decide⟩,⟨369,by decide⟩,⟨5,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨368,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨371,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨372,by decide⟩,⟨373,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨374,by decide⟩,⟨374,by decide⟩,⟨374,by decide⟩] | _ => ![⟨0,by decide⟩,⟨375,by decide⟩,⟨375,by decide⟩]

def ntree15LLRLRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLRLRRLL i else ntree15LLRLRRLR (i - 7)

def ntree15LLRLRRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨374,by decide⟩,⟨376,by decide⟩,⟨376,by decide⟩] | 1 => ![⟨377,by decide⟩,⟨374,by decide⟩,⟨377,by decide⟩] | 2 => ![⟨5,by decide⟩,⟨375,by decide⟩,⟨378,by decide⟩] | 3 => ![⟨377,by decide⟩,⟨376,by decide⟩,⟨379,by decide⟩] | 4 => ![⟨32,by decide⟩,⟨380,by decide⟩,⟨375,by decide⟩] | 5 => ![⟨381,by decide⟩,⟨374,by decide⟩,⟨374,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨382,by decide⟩] | _ => ![⟨374,by decide⟩,⟨374,by decide⟩,⟨383,by decide⟩]

def ntree15LLRLRRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨384,by decide⟩,⟨374,by decide⟩,⟨384,by decide⟩] | 1 => ![⟨385,by decide⟩,⟨0,by decide⟩,⟨385,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨386,by decide⟩] | 3 => ![⟨385,by decide⟩,⟨1,by decide⟩,⟨387,by decide⟩] | 4 => ![⟨388,by decide⟩,⟨389,by decide⟩,⟨388,by decide⟩] | 5 => ![⟨5,by decide⟩,⟨390,by decide⟩,⟨391,by decide⟩] | 6 => ![⟨388,by decide⟩,⟨392,by decide⟩,⟨393,by decide⟩] | _ => ![⟨385,by decide⟩,⟨369,by decide⟩,⟨385,by decide⟩]

def ntree15LLRLRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 8 then ntree15LLRLRRRL i else ntree15LLRLRRRR (i - 8)

def ntree15LLRLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LLRLRRL i else ntree15LLRLRRR (i - 15)

def ntree15LLRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15LLRLRL i else ntree15LLRLRR (i - 30)

def ntree15LLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 60 then ntree15LLRLL i else ntree15LLRLR (i - 60)

def ntree15LLRRLLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨394,by decide⟩,⟨46,by decide⟩,⟨385,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨395,by decide⟩] | 2 => ![⟨46,by decide⟩,⟨46,by decide⟩,⟨395,by decide⟩] | 3 => ![⟨396,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨397,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨398,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LLRRLLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨399,by decide⟩,⟨46,by decide⟩,⟨400,by decide⟩] | 1 => ![⟨400,by decide⟩,⟨0,by decide⟩,⟨400,by decide⟩] | 2 => ![⟨389,by decide⟩,⟨389,by decide⟩,⟨389,by decide⟩] | 3 => ![⟨389,by decide⟩,⟨389,by decide⟩,⟨401,by decide⟩] | 4 => ![⟨402,by decide⟩,⟨403,by decide⟩,⟨402,by decide⟩] | 5 => ![⟨403,by decide⟩,⟨403,by decide⟩,⟨403,by decide⟩] | 6 => ![⟨404,by decide⟩,⟨405,by decide⟩,⟨404,by decide⟩] | _ => ![⟨406,by decide⟩,⟨403,by decide⟩,⟨406,by decide⟩]

def ntree15LLRRLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLRRLLLL i else ntree15LLRRLLLR (i - 7)

def ntree15LLRRLLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨407,by decide⟩,⟨408,by decide⟩,⟨402,by decide⟩] | 1 => ![⟨409,by decide⟩,⟨403,by decide⟩,⟨403,by decide⟩] | 2 => ![⟨410,by decide⟩,⟨410,by decide⟩,⟨374,by decide⟩] | 3 => ![⟨46,by decide⟩,⟨411,by decide⟩,⟨375,by decide⟩] | 4 => ![⟨410,by decide⟩,⟨412,by decide⟩,⟨376,by decide⟩] | 5 => ![⟨413,by decide⟩,⟨413,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨414,by decide⟩,⟨0,by decide⟩]

def ntree15LLRRLLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨413,by decide⟩,⟨415,by decide⟩,⟨1,by decide⟩] | 1 => ![⟨416,by decide⟩,⟨374,by decide⟩,⟨416,by decide⟩] | 2 => ![⟨70,by decide⟩,⟨375,by decide⟩,⟨417,by decide⟩] | 3 => ![⟨416,by decide⟩,⟨376,by decide⟩,⟨418,by decide⟩] | 4 => ![⟨419,by decide⟩,⟨410,by decide⟩,⟨416,by decide⟩] | 5 => ![⟨420,by decide⟩,⟨413,by decide⟩,⟨70,by decide⟩] | 6 => ![⟨421,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨422,by decide⟩,⟨413,by decide⟩,⟨10,by decide⟩]

def ntree15LLRRLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLRRLLRL i else ntree15LLRRLLRR (i - 7)

def ntree15LLRRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LLRRLLL i else ntree15LLRRLLR (i - 15)

def ntree15LLRRLRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨423,by decide⟩,⟨374,by decide⟩,⟨374,by decide⟩] | 2 => ![⟨424,by decide⟩,⟨410,by decide⟩,⟨384,by decide⟩] | 3 => ![⟨374,by decide⟩,⟨374,by decide⟩,⟨425,by decide⟩] | 4 => ![⟨426,by decide⟩,⟨389,by decide⟩,⟨426,by decide⟩] | 5 => ![⟨427,by decide⟩,⟨0,by decide⟩,⟨427,by decide⟩] | _ => ![⟨0,by decide⟩,⟨428,by decide⟩,⟨0,by decide⟩]

def ntree15LLRRLRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨429,by decide⟩,⟨430,by decide⟩,⟨1,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨431,by decide⟩] | 2 => ![⟨432,by decide⟩,⟨0,by decide⟩,⟨432,by decide⟩] | 3 => ![⟨432,by decide⟩,⟨1,by decide⟩,⟨433,by decide⟩] | 4 => ![⟨432,by decide⟩,⟨368,by decide⟩,⟨432,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨434,by decide⟩,⟨435,by decide⟩] | 6 => ![⟨436,by decide⟩,⟨437,by decide⟩,⟨436,by decide⟩] | _ => ![⟨436,by decide⟩,⟨438,by decide⟩,⟨439,by decide⟩]

def ntree15LLRRLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLRRLRLL i else ntree15LLRRLRLR (i - 7)

def ntree15LLRRLRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨440,by decide⟩,⟨441,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨442,by decide⟩,⟨441,by decide⟩,⟨432,by decide⟩] | 2 => ![⟨443,by decide⟩,⟨0,by decide⟩,⟨443,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨444,by decide⟩] | 4 => ![⟨443,by decide⟩,⟨1,by decide⟩,⟨445,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨434,by decide⟩,⟨434,by decide⟩]

def ntree15LLRRLRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨437,by decide⟩,⟨437,by decide⟩,⟨437,by decide⟩] | 1 => ![⟨437,by decide⟩,⟨438,by decide⟩,⟨438,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨446,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨447,by decide⟩] | 6 => ![⟨432,by decide⟩,⟨90,by decide⟩,⟨448,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LLRRLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLRRLRRL i else ntree15LLRRLRRR (i - 7)

def ntree15LLRRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LLRRLRL i else ntree15LLRRLRR (i - 15)

def ntree15LLRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15LLRRLL i else ntree15LLRRLR (i - 30)

def ntree15LLRRRLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨46,by decide⟩,⟨449,by decide⟩,⟨450,by decide⟩] | 1 => ![⟨451,by decide⟩,⟨452,by decide⟩,⟨453,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨454,by decide⟩,⟨455,by decide⟩] | 3 => ![⟨385,by decide⟩,⟨454,by decide⟩,⟨456,by decide⟩] | 4 => ![⟨432,by decide⟩,⟨454,by decide⟩,⟨457,by decide⟩] | 5 => ![⟨458,by decide⟩,⟨459,by decide⟩,⟨460,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LLRRRLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨461,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨461,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨462,by decide⟩,⟨46,by decide⟩,⟨432,by decide⟩] | 3 => ![⟨463,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨464,by decide⟩,⟨441,by decide⟩,⟨385,by decide⟩] | 5 => ![⟨465,by decide⟩,⟨466,by decide⟩,⟨467,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨468,by decide⟩,⟨0,by decide⟩] | _ => ![⟨385,by decide⟩,⟨468,by decide⟩,⟨385,by decide⟩]

def ntree15LLRRRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLRRRLLL i else ntree15LLRRRLLR (i - 7)

def ntree15LLRRRLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨10,by decide⟩,⟨468,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨469,by decide⟩,⟨470,by decide⟩,⟨469,by decide⟩] | 2 => ![⟨470,by decide⟩,⟨470,by decide⟩,⟨470,by decide⟩] | 3 => ![⟨471,by decide⟩,⟨472,by decide⟩,⟨471,by decide⟩] | 4 => ![⟨473,by decide⟩,⟨470,by decide⟩,⟨473,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨474,by decide⟩] | _ => ![⟨475,by decide⟩,⟨437,by decide⟩,⟨475,by decide⟩]

def ntree15LLRRRLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨476,by decide⟩,⟨0,by decide⟩,⟨476,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨477,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨374,by decide⟩,⟨478,by decide⟩,⟨374,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨479,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨480,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨481,by decide⟩,⟨374,by decide⟩,⟨481,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨482,by decide⟩,⟨0,by decide⟩] | _ => ![⟨432,by decide⟩,⟨482,by decide⟩,⟨432,by decide⟩]

def ntree15LLRRRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLRRRLRL i else ntree15LLRRRLRR (i - 7)

def ntree15LLRRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LLRRRLL i else ntree15LLRRRLR (i - 15)

def ntree15LLRRRRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨5,by decide⟩,⟨482,by decide⟩,⟨5,by decide⟩] | 1 => ![⟨483,by decide⟩,⟨484,by decide⟩,⟨469,by decide⟩] | 2 => ![⟨485,by decide⟩,⟨486,by decide⟩,⟨5,by decide⟩] | 3 => ![⟨484,by decide⟩,⟨484,by decide⟩,⟨470,by decide⟩] | 4 => ![⟨486,by decide⟩,⟨486,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LLRRRRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨487,by decide⟩,⟨141,by decide⟩,⟨432,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨5,by decide⟩,⟨468,by decide⟩,⟨5,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨482,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨15,by decide⟩,⟨488,by decide⟩,⟨15,by decide⟩] | 6 => ![⟨46,by decide⟩,⟨46,by decide⟩,⟨474,by decide⟩] | _ => ![⟨413,by decide⟩,⟨489,by decide⟩,⟨87,by decide⟩]

def ntree15LLRRRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LLRRRRLL i else ntree15LLRRRRLR (i - 7)

def ntree15LLRRRRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨490,by decide⟩,⟨490,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨490,by decide⟩,⟨491,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨492,by decide⟩,⟨492,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨493,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨494,by decide⟩,⟨494,by decide⟩,⟨374,by decide⟩] | 5 => ![⟨490,by decide⟩,⟨495,by decide⟩,⟨375,by decide⟩] | 6 => ![⟨494,by decide⟩,⟨496,by decide⟩,⟨376,by decide⟩] | _ => ![⟨374,by decide⟩,⟨497,by decide⟩,⟨374,by decide⟩]

def ntree15LLRRRRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨498,by decide⟩,⟨498,by decide⟩,⟨498,by decide⟩] | 1 => ![⟨163,by decide⟩,⟨163,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨499,by decide⟩,⟨498,by decide⟩,⟨499,by decide⟩] | 3 => ![⟨500,by decide⟩,⟨0,by decide⟩,⟨500,by decide⟩] | 4 => ![⟨501,by decide⟩,⟨0,by decide⟩,⟨501,by decide⟩] | 5 => ![⟨502,by decide⟩,⟨0,by decide⟩,⟨502,by decide⟩] | 6 => ![⟨503,by decide⟩,⟨0,by decide⟩,⟨503,by decide⟩] | _ => ![⟨504,by decide⟩,⟨0,by decide⟩,⟨504,by decide⟩]

def ntree15LLRRRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 8 then ntree15LLRRRRRL i else ntree15LLRRRRRR (i - 8)

def ntree15LLRRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LLRRRRL i else ntree15LLRRRRR (i - 15)

def ntree15LLRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15LLRRRL i else ntree15LLRRRR (i - 30)

def ntree15LLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 60 then ntree15LLRRL i else ntree15LLRRR (i - 60)

def ntree15LLR (i : Nat) : Fin 3 → Fin 1868 := if i < 121 then ntree15LLRL i else ntree15LLRR (i - 121)

def ntree15LL (i : Nat) : Fin 3 → Fin 1868 := if i < 242 then ntree15LLL i else ntree15LLR (i - 242)

def ntree15LRLLLLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨504,by decide⟩,⟨1,by decide⟩,⟨505,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨506,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨390,by decide⟩,⟨390,by decide⟩] | 3 => ![⟨389,by decide⟩,⟨392,by decide⟩,⟨392,by decide⟩] | 4 => ![⟨507,by decide⟩,⟨507,by decide⟩,⟨498,by decide⟩] | 5 => ![⟨508,by decide⟩,⟨508,by decide⟩,⟨0,by decide⟩] | _ => ![⟨509,by decide⟩,⟨509,by decide⟩,⟨0,by decide⟩]

def ntree15LRLLLLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨510,by decide⟩,⟨510,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨511,by decide⟩,⟨511,by decide⟩,⟨389,by decide⟩] | 2 => ![⟨512,by decide⟩,⟨163,by decide⟩,⟨504,by decide⟩] | 3 => ![⟨513,by decide⟩,⟨492,by decide⟩,⟨503,by decide⟩] | 4 => ![⟨503,by decide⟩,⟨375,by decide⟩,⟨514,by decide⟩] | 5 => ![⟨515,by decide⟩,⟨490,by decide⟩,⟨432,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨215,by decide⟩,⟨215,by decide⟩] | _ => ![⟨217,by decide⟩,⟨219,by decide⟩,⟨219,by decide⟩]

def ntree15LRLLLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRLLLLLL i else ntree15LRLLLLLR (i - 7)

def ntree15LRLLLLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨516,by decide⟩,⟨217,by decide⟩,⟨516,by decide⟩] | 1 => ![⟨504,by decide⟩,⟨222,by decide⟩,⟨517,by decide⟩] | 2 => ![⟨518,by decide⟩,⟨223,by decide⟩,⟨518,by decide⟩] | 3 => ![⟨518,by decide⟩,⟨224,by decide⟩,⟨519,by decide⟩] | 4 => ![⟨223,by decide⟩,⟨223,by decide⟩,⟨520,by decide⟩] | 5 => ![⟨432,by decide⟩,⟨0,by decide⟩,⟨432,by decide⟩] | _ => ![⟨492,by decide⟩,⟨521,by decide⟩,⟨222,by decide⟩]

def ntree15LRLLLLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨522,by decide⟩] | 1 => ![⟨523,by decide⟩,⟨0,by decide⟩,⟨523,by decide⟩] | 2 => ![⟨524,by decide⟩,⟨524,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨525,by decide⟩,⟨525,by decide⟩,⟨437,by decide⟩] | 4 => ![⟨526,by decide⟩,⟨526,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨527,by decide⟩,⟨527,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨528,by decide⟩,⟨528,by decide⟩,⟨374,by decide⟩] | _ => ![⟨432,by decide⟩,⟨0,by decide⟩,⟨432,by decide⟩]

def ntree15LRLLLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRLLLLRL i else ntree15LRLLLLRR (i - 7)

def ntree15LRLLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LRLLLLL i else ntree15LRLLLLR (i - 15)

def ntree15LRLLLRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨529,by decide⟩,⟨163,by decide⟩,⟨432,by decide⟩] | 1 => ![⟨530,by decide⟩,⟨494,by decide⟩,⟨481,by decide⟩] | 2 => ![⟨531,by decide⟩,⟨374,by decide⟩,⟨374,by decide⟩] | 3 => ![⟨532,by decide⟩,⟨524,by decide⟩,⟨432,by decide⟩] | 4 => ![⟨533,by decide⟩,⟨525,by decide⟩,⟨436,by decide⟩] | 5 => ![⟨534,by decide⟩,⟨163,by decide⟩,⟨432,by decide⟩] | _ => ![⟨535,by decide⟩,⟨526,by decide⟩,⟨10,by decide⟩]

def ntree15LRLLLRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨536,by decide⟩,⟨527,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨537,by decide⟩,⟨374,by decide⟩,⟨374,by decide⟩] | 2 => ![⟨538,by decide⟩,⟨528,by decide⟩,⟨384,by decide⟩] | 3 => ![⟨539,by decide⟩,⟨539,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨540,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨163,by decide⟩,⟨163,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨541,by decide⟩,⟨0,by decide⟩,⟨541,by decide⟩] | _ => ![⟨542,by decide⟩,⟨194,by decide⟩,⟨542,by decide⟩]

def ntree15LRLLLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRLLLRLL i else ntree15LRLLLRLR (i - 7)

def ntree15LRLLLRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨543,by decide⟩,⟨0,by decide⟩,⟨543,by decide⟩] | 1 => ![⟨544,by decide⟩,⟨0,by decide⟩,⟨544,by decide⟩] | 2 => ![⟨545,by decide⟩,⟨223,by decide⟩,⟨545,by decide⟩] | 3 => ![⟨546,by decide⟩,⟨163,by decide⟩,⟨541,by decide⟩] | 4 => ![⟨547,by decide⟩,⟨193,by decide⟩,⟨542,by decide⟩] | 5 => ![⟨548,by decide⟩,⟨163,by decide⟩,⟨432,by decide⟩] | _ => ![⟨549,by decide⟩,⟨46,by decide⟩,⟨543,by decide⟩]

def ntree15LRLLLRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨550,by decide⟩,⟨163,by decide⟩,⟨432,by decide⟩] | 1 => ![⟨551,by decide⟩,⟨273,by decide⟩,⟨518,by decide⟩] | 2 => ![⟨552,by decide⟩,⟨223,by decide⟩,⟨223,by decide⟩] | 3 => ![⟨553,by decide⟩,⟨46,by decide⟩,⟨544,by decide⟩] | 4 => ![⟨554,by decide⟩,⟨223,by decide⟩,⟨223,by decide⟩] | 5 => ![⟨555,by decide⟩,⟨230,by decide⟩,⟨545,by decide⟩] | 6 => ![⟨556,by decide⟩,⟨556,by decide⟩,⟨556,by decide⟩] | _ => ![⟨557,by decide⟩,⟨557,by decide⟩,⟨557,by decide⟩]

def ntree15LRLLLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRLLLRRL i else ntree15LRLLLRRR (i - 7)

def ntree15LRLLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LRLLLRL i else ntree15LRLLLRR (i - 15)

def ntree15LRLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15LRLLLL i else ntree15LRLLLR (i - 30)

def ntree15LRLLRLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨558,by decide⟩,⟨558,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨559,by decide⟩,⟨559,by decide⟩,⟨223,by decide⟩] | 2 => ![⟨560,by decide⟩,⟨560,by decide⟩,⟨556,by decide⟩] | 3 => ![⟨561,by decide⟩,⟨561,by decide⟩,⟨557,by decide⟩] | 4 => ![⟨562,by decide⟩,⟨0,by decide⟩,⟨562,by decide⟩] | 5 => ![⟨563,by decide⟩,⟨374,by decide⟩,⟨563,by decide⟩] | _ => ![⟨564,by decide⟩,⟨556,by decide⟩,⟨564,by decide⟩]

def ntree15LRLLRLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨565,by decide⟩,⟨557,by decide⟩,⟨565,by decide⟩] | 1 => ![⟨566,by decide⟩,⟨46,by decide⟩,⟨562,by decide⟩] | 2 => ![⟨567,by decide⟩,⟨374,by decide⟩,⟨374,by decide⟩] | 3 => ![⟨568,by decide⟩,⟨410,by decide⟩,⟨563,by decide⟩] | 4 => ![⟨569,by decide⟩,⟨558,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨570,by decide⟩,⟨223,by decide⟩,⟨223,by decide⟩] | 6 => ![⟨571,by decide⟩,⟨559,by decide⟩,⟨239,by decide⟩] | _ => ![⟨572,by decide⟩,⟨560,by decide⟩,⟨564,by decide⟩]

def ntree15LRLLRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRLLRLLL i else ntree15LRLLRLLR (i - 7)

def ntree15LRLLRLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨573,by decide⟩,⟨557,by decide⟩,⟨557,by decide⟩] | 1 => ![⟨574,by decide⟩,⟨561,by decide⟩,⟨565,by decide⟩] | 2 => ![⟨575,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨576,by decide⟩,⟨490,by decide⟩,⟨5,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨577,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨578,by decide⟩,⟨374,by decide⟩,⟨374,by decide⟩] | _ => ![⟨579,by decide⟩,⟨494,by decide⟩,⟨377,by decide⟩]

def ntree15LRLLRLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨580,by decide⟩,⟨498,by decide⟩,⟨580,by decide⟩] | 1 => ![⟨581,by decide⟩,⟨0,by decide⟩,⟨581,by decide⟩] | 2 => ![⟨582,by decide⟩,⟨0,by decide⟩,⟨582,by decide⟩] | 3 => ![⟨583,by decide⟩,⟨0,by decide⟩,⟨583,by decide⟩] | 4 => ![⟨584,by decide⟩,⟨163,by decide⟩,⟨583,by decide⟩] | 5 => ![⟨374,by decide⟩,⟨585,by decide⟩,⟨374,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨586,by decide⟩,⟨586,by decide⟩] | _ => ![⟨587,by decide⟩,⟨194,by decide⟩,⟨587,by decide⟩]

def ntree15LRLLRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRLLRLRL i else ntree15LRLLRLRR (i - 7)

def ntree15LRLLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LRLLRLL i else ntree15LRLLRLR (i - 15)

def ntree15LRLLRRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨588,by decide⟩,⟨510,by decide⟩,⟨385,by decide⟩] | 1 => ![⟨589,by decide⟩,⟨507,by decide⟩,⟨580,by decide⟩] | 2 => ![⟨590,by decide⟩,⟨46,by decide⟩,⟨581,by decide⟩] | 3 => ![⟨591,by decide⟩,⟨508,by decide⟩,⟨5,by decide⟩] | 4 => ![⟨592,by decide⟩,⟨509,by decide⟩,⟨5,by decide⟩] | 5 => ![⟨593,by decide⟩,⟨163,by decide⟩,⟨385,by decide⟩] | _ => ![⟨594,by decide⟩,⟨511,by decide⟩,⟨388,by decide⟩]

def ntree15LRLLRRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨595,by decide⟩,⟨46,by decide⟩,⟨582,by decide⟩] | 1 => ![⟨596,by decide⟩,⟨193,by decide⟩,⟨587,by decide⟩] | 2 => ![⟨597,by decide⟩,⟨163,by decide⟩,⟨385,by decide⟩] | 3 => ![⟨598,by decide⟩,⟨0,by decide⟩,⟨598,by decide⟩] | 4 => ![⟨385,by decide⟩,⟨0,by decide⟩,⟨385,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨599,by decide⟩,⟨0,by decide⟩,⟨599,by decide⟩] | _ => ![⟨0,by decide⟩,⟨600,by decide⟩,⟨600,by decide⟩]

def ntree15LRLLRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRLLRRLL i else ntree15LRLLRRLR (i - 7)

def ntree15LRLLRRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨601,by decide⟩,⟨601,by decide⟩] | 1 => ![⟨492,by decide⟩,⟨602,by decide⟩,⟨601,by decide⟩] | 2 => ![⟨599,by decide⟩,⟨601,by decide⟩,⟨603,by decide⟩] | 3 => ![⟨604,by decide⟩,⟨0,by decide⟩,⟨604,by decide⟩] | 4 => ![⟨437,by decide⟩,⟨437,by decide⟩,⟨605,by decide⟩] | 5 => ![⟨606,by decide⟩,⟨213,by decide⟩,⟨604,by decide⟩] | 6 => ![⟨213,by decide⟩,⟨607,by decide⟩,⟨601,by decide⟩] | _ => ![⟨608,by decide⟩,⟨490,by decide⟩,⟨443,by decide⟩]

def ntree15LRLLRRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨443,by decide⟩,⟨601,by decide⟩,⟨609,by decide⟩] | 1 => ![⟨498,by decide⟩,⟨610,by decide⟩,⟨610,by decide⟩] | 2 => ![⟨217,by decide⟩,⟨611,by decide⟩,⟨217,by decide⟩] | 3 => ![⟨498,by decide⟩,⟨612,by decide⟩,⟨612,by decide⟩] | 4 => ![⟨613,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨614,by decide⟩,⟨46,by decide⟩,⟨604,by decide⟩] | 6 => ![⟨615,by decide⟩,⟨223,by decide⟩,⟨615,by decide⟩] | _ => ![⟨616,by decide⟩,⟨223,by decide⟩,⟨223,by decide⟩]

def ntree15LRLLRRR (i : Nat) : Fin 3 → Fin 1868 := if i < 8 then ntree15LRLLRRRL i else ntree15LRLLRRRR (i - 8)

def ntree15LRLLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LRLLRRL i else ntree15LRLLRRR (i - 15)

def ntree15LRLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15LRLLRL i else ntree15LRLLRR (i - 30)

def ntree15LRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 60 then ntree15LRLLL i else ntree15LRLLR (i - 60)

def ntree15LRLRLLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨617,by decide⟩,⟨230,by decide⟩,⟨615,by decide⟩] | 1 => ![⟨385,by decide⟩,⟨0,by decide⟩,⟨385,by decide⟩] | 2 => ![⟨46,by decide⟩,⟨618,by decide⟩,⟨600,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨619,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨385,by decide⟩,⟨600,by decide⟩,⟨620,by decide⟩] | 5 => ![⟨621,by decide⟩,⟨0,by decide⟩,⟨621,by decide⟩] | _ => ![⟨622,by decide⟩,⟨217,by decide⟩,⟨622,by decide⟩]

def ntree15LRLRLLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨623,by decide⟩,⟨0,by decide⟩,⟨623,by decide⟩] | 1 => ![⟨624,by decide⟩,⟨0,by decide⟩,⟨624,by decide⟩] | 2 => ![⟨625,by decide⟩,⟨223,by decide⟩,⟨625,by decide⟩] | 3 => ![⟨5,by decide⟩,⟨600,by decide⟩,⟨626,by decide⟩] | 4 => ![⟨163,by decide⟩,⟨627,by decide⟩,⟨600,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨628,by decide⟩,⟨0,by decide⟩,⟨628,by decide⟩] | _ => ![⟨629,by decide⟩,⟨374,by decide⟩,⟨629,by decide⟩]

def ntree15LRLRLLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRLRLLLL i else ntree15LRLRLLLR (i - 7)

def ntree15LRLRLLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨630,by decide⟩,⟨556,by decide⟩,⟨630,by decide⟩] | 1 => ![⟨631,by decide⟩,⟨557,by decide⟩,⟨631,by decide⟩] | 2 => ![⟨632,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨633,by decide⟩,⟨634,by decide⟩,⟨5,by decide⟩] | 4 => ![⟨635,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨635,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨636,by decide⟩]

def ntree15LRLRLLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨374,by decide⟩,⟨374,by decide⟩,⟨637,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨638,by decide⟩,⟨638,by decide⟩] | 2 => ![⟨374,by decide⟩,⟨639,by decide⟩,⟨639,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨638,by decide⟩,⟨640,by decide⟩] | 4 => ![⟨384,by decide⟩,⟨639,by decide⟩,⟨641,by decide⟩] | 5 => ![⟨642,by decide⟩,⟨374,by decide⟩,⟨374,by decide⟩] | 6 => ![⟨35,by decide⟩,⟨643,by decide⟩,⟨638,by decide⟩] | _ => ![⟨0,by decide⟩,⟨644,by decide⟩,⟨0,by decide⟩]

def ntree15LRLRLLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRLRLLRL i else ntree15LRLRLLRR (i - 7)

def ntree15LRLRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LRLRLLL i else ntree15LRLRLLR (i - 15)

def ntree15LRLRLRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨645,by decide⟩,⟨646,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨647,by decide⟩,⟨648,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨649,by decide⟩,⟨648,by decide⟩,⟨385,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨650,by decide⟩] | 4 => ![⟨385,by decide⟩,⟨2,by decide⟩,⟨651,by decide⟩] | 5 => ![⟨5,by decide⟩,⟨652,by decide⟩,⟨653,by decide⟩] | _ => ![⟨388,by decide⟩,⟨654,by decide⟩,⟨655,by decide⟩]

def ntree15LRLRLRLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨656,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨657,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨385,by decide⟩,⟨56,by decide⟩,⟨658,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨659,by decide⟩] | _ => ![⟨400,by decide⟩,⟨2,by decide⟩,⟨660,by decide⟩]

def ntree15LRLRLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRLRLRLL i else ntree15LRLRLRLR (i - 7)

def ntree15LRLRLRRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨0,by decide⟩,⟨652,by decide⟩,⟨652,by decide⟩] | 1 => ![⟨389,by decide⟩,⟨654,by decide⟩,⟨654,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨661,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨662,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨374,by decide⟩,⟨663,by decide⟩,⟨374,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨664,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨665,by decide⟩,⟨0,by decide⟩]

def ntree15LRLRLRRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨666,by decide⟩,⟨76,by decide⟩,⟨432,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨667,by decide⟩] | 2 => ![⟨76,by decide⟩,⟨76,by decide⟩,⟨667,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨668,by decide⟩] | 4 => ![⟨432,by decide⟩,⟨2,by decide⟩,⟨669,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨670,by decide⟩,⟨671,by decide⟩] | 6 => ![⟨436,by decide⟩,⟨672,by decide⟩,⟨673,by decide⟩] | _ => ![⟨674,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LRLRLRR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRLRLRRL i else ntree15LRLRLRRR (i - 7)

def ntree15LRLRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LRLRLRL i else ntree15LRLRLRR (i - 15)

def ntree15LRLRL (i : Nat) : Fin 3 → Fin 1868 := if i < 30 then ntree15LRLRLL i else ntree15LRLRLR (i - 30)

def ntree15LRLRRLLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨675,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨676,by decide⟩,⟨76,by decide⟩,⟨443,by decide⟩] | 2 => ![⟨677,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨437,by decide⟩,⟨437,by decide⟩,⟨678,by decide⟩] | 4 => ![⟨76,by decide⟩,⟨679,by decide⟩,⟨680,by decide⟩] | 5 => ![⟨681,by decide⟩,⟨682,by decide⟩,⟨683,by decide⟩] | _ => ![⟨684,by decide⟩,⟨76,by decide⟩,⟨385,by decide⟩]

def ntree15LRLRRLLR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨685,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨686,by decide⟩,⟨648,by decide⟩,⟨432,by decide⟩] | 2 => ![⟨687,by decide⟩,⟨688,by decide⟩,⟨689,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨690,by decide⟩,⟨691,by decide⟩] | 4 => ![⟨432,by decide⟩,⟨690,by decide⟩,⟨692,by decide⟩] | 5 => ![⟨385,by decide⟩,⟨690,by decide⟩,⟨693,by decide⟩] | 6 => ![⟨694,by decide⟩,⟨695,by decide⟩,⟨696,by decide⟩] | _ => ![⟨697,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LRLRRLL (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRLRRLLL i else ntree15LRLRRLLR (i - 7)

def ntree15LRLRRLRL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨697,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨698,by decide⟩,⟨699,by decide⟩,⟨402,by decide⟩] | 2 => ![⟨700,by decide⟩,⟨701,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨699,by decide⟩,⟨699,by decide⟩,⟨403,by decide⟩] | 4 => ![⟨701,by decide⟩,⟨701,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LRLRRLRR (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨702,by decide⟩,⟨119,by decide⟩,⟨385,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨703,by decide⟩,⟨704,by decide⟩,⟨469,by decide⟩] | 3 => ![⟨705,by decide⟩,⟨470,by decide⟩,⟨470,by decide⟩] | 4 => ![⟨706,by decide⟩,⟨706,by decide⟩,⟨374,by decide⟩] | 5 => ![⟨707,by decide⟩,⟨707,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨708,by decide⟩,⟨707,by decide⟩,⟨5,by decide⟩] | _ => ![⟨709,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree15LRLRRLR (i : Nat) : Fin 3 → Fin 1868 := if i < 7 then ntree15LRLRRLRL i else ntree15LRLRRLRR (i - 7)

def ntree15LRLRRL (i : Nat) : Fin 3 → Fin 1868 := if i < 15 then ntree15LRLRRLL i else ntree15LRLRRLR (i - 15)

def ntree15LRLRRRLL (i : Nat) : Fin 3 → Fin 1868 := match i with | 0 => ![⟨710,by decide⟩,⟨706,by decide⟩,⟨377,by decide⟩] | 1 => ![⟨711,by decide⟩,⟨374,by decide⟩,⟨374,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨374,by decide⟩,⟨374,by decide⟩,⟨712,by decide⟩] | 4 => ![⟨76,by decide⟩,⟨713,by decide⟩,⟨638,by decide⟩] | 5 => ![⟨706,by decide⟩,⟨714,by decide⟩,⟨639,by decide⟩] | _ => ![⟨0,by decide⟩,⟨715,by decide⟩,⟨0,by decide⟩]

end Paper2.Certificates.Q6.Coverage
