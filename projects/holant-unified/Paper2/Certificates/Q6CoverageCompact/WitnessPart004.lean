import Paper2.Certificates.Q6CoverageCompact.WitnessPart003

namespace Paper2.Certificates.Q6.Coverage

def witnessTreeLRLRRRLL (i : Nat) : OrbitWitness := match i with | 0 => witness670 | 1 => witness671 | 2 => witness672 | 3 => witness673 | 4 => witness674 | 5 => witness675 | _ => witness676

def witnessTreeLRLRRRLR (i : Nat) : OrbitWitness := match i with | 0 => witness677 | 1 => witness678 | 2 => witness679 | 3 => witness680 | 4 => witness681 | 5 => witness682 | 6 => witness683 | _ => witness684

def witnessTreeLRLRRRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeLRLRRRLL i else witnessTreeLRLRRRLR (i - 7)

def witnessTreeLRLRRRRL (i : Nat) : OrbitWitness := match i with | 0 => witness685 | 1 => witness686 | 2 => witness687 | 3 => witness688 | 4 => witness689 | 5 => witness690 | _ => witness691

def witnessTreeLRLRRRRR (i : Nat) : OrbitWitness := match i with | 0 => witness692 | 1 => witness693 | 2 => witness694 | 3 => witness695 | 4 => witness696 | 5 => witness697 | 6 => witness698 | _ => witness699

def witnessTreeLRLRRRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeLRLRRRRL i else witnessTreeLRLRRRRR (i - 7)

def witnessTreeLRLRRR (i : Nat) : OrbitWitness := if i < 15 then witnessTreeLRLRRRL i else witnessTreeLRLRRRR (i - 15)

def witnessTreeLRLRR (i : Nat) : OrbitWitness := if i < 29 then witnessTreeLRLRRL i else witnessTreeLRLRRR (i - 29)

def witnessTreeLRLR (i : Nat) : OrbitWitness := if i < 58 then witnessTreeLRLRL i else witnessTreeLRLRR (i - 58)

def witnessTreeLRL (i : Nat) : OrbitWitness := if i < 116 then witnessTreeLRLL i else witnessTreeLRLR (i - 116)

def witnessTreeLRRLLLLL (i : Nat) : OrbitWitness := match i with | 0 => witness700 | 1 => witness701 | 2 => witness702 | 3 => witness703 | 4 => witness704 | 5 => witness705 | _ => witness706

def witnessTreeLRRLLLLR (i : Nat) : OrbitWitness := match i with | 0 => witness707 | 1 => witness708 | 2 => witness709 | 3 => witness710 | 4 => witness711 | 5 => witness712 | _ => witness713

def witnessTreeLRRLLLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeLRRLLLLL i else witnessTreeLRRLLLLR (i - 7)

def witnessTreeLRRLLLRL (i : Nat) : OrbitWitness := match i with | 0 => witness714 | 1 => witness715 | 2 => witness716 | 3 => witness717 | 4 => witness718 | 5 => witness719 | _ => witness720

def witnessTreeLRRLLLRR (i : Nat) : OrbitWitness := match i with | 0 => witness721 | 1 => witness722 | 2 => witness723 | 3 => witness724 | 4 => witness725 | 5 => witness726 | 6 => witness727 | _ => witness728

def witnessTreeLRRLLLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeLRRLLLRL i else witnessTreeLRRLLLRR (i - 7)

def witnessTreeLRRLLL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeLRRLLLL i else witnessTreeLRRLLLR (i - 14)

def witnessTreeLRRLLRLL (i : Nat) : OrbitWitness := match i with | 0 => witness729 | 1 => witness730 | 2 => witness731 | 3 => witness732 | 4 => witness733 | 5 => witness734 | _ => witness735

def witnessTreeLRRLLRLR (i : Nat) : OrbitWitness := match i with | 0 => witness736 | 1 => witness737 | 2 => witness738 | 3 => witness739 | 4 => witness740 | 5 => witness741 | _ => witness742

def witnessTreeLRRLLRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeLRRLLRLL i else witnessTreeLRRLLRLR (i - 7)

def witnessTreeLRRLLRRL (i : Nat) : OrbitWitness := match i with | 0 => witness743 | 1 => witness744 | 2 => witness745 | 3 => witness746 | 4 => witness747 | 5 => witness748 | _ => witness749

def witnessTreeLRRLLRRR (i : Nat) : OrbitWitness := match i with | 0 => witness750 | 1 => witness751 | 2 => witness752 | 3 => witness753 | 4 => witness754 | 5 => witness755 | 6 => witness756 | _ => witness757

def witnessTreeLRRLLRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeLRRLLRRL i else witnessTreeLRRLLRRR (i - 7)

def witnessTreeLRRLLR (i : Nat) : OrbitWitness := if i < 14 then witnessTreeLRRLLRL i else witnessTreeLRRLLRR (i - 14)

def witnessTreeLRRLL (i : Nat) : OrbitWitness := if i < 29 then witnessTreeLRRLLL i else witnessTreeLRRLLR (i - 29)

def witnessTreeLRRLRLLL (i : Nat) : OrbitWitness := match i with | 0 => witness758 | 1 => witness759 | 2 => witness760 | 3 => witness761 | 4 => witness762 | 5 => witness763 | _ => witness764

def witnessTreeLRRLRLLR (i : Nat) : OrbitWitness := match i with | 0 => witness765 | 1 => witness766 | 2 => witness767 | 3 => witness768 | 4 => witness769 | 5 => witness770 | _ => witness771

def witnessTreeLRRLRLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeLRRLRLLL i else witnessTreeLRRLRLLR (i - 7)

def witnessTreeLRRLRLRL (i : Nat) : OrbitWitness := match i with | 0 => witness772 | 1 => witness773 | 2 => witness774 | 3 => witness775 | 4 => witness776 | 5 => witness777 | _ => witness778

def witnessTreeLRRLRLRR (i : Nat) : OrbitWitness := match i with | 0 => witness779 | 1 => witness780 | 2 => witness781 | 3 => witness782 | 4 => witness783 | 5 => witness784 | 6 => witness785 | _ => witness786

def witnessTreeLRRLRLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeLRRLRLRL i else witnessTreeLRRLRLRR (i - 7)

def witnessTreeLRRLRL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeLRRLRLL i else witnessTreeLRRLRLR (i - 14)

def witnessTreeLRRLRRLL (i : Nat) : OrbitWitness := match i with | 0 => witness787 | 1 => witness788 | 2 => witness789 | 3 => witness790 | 4 => witness791 | 5 => witness792 | _ => witness793

def witnessTreeLRRLRRLR (i : Nat) : OrbitWitness := match i with | 0 => witness794 | 1 => witness795 | 2 => witness796 | 3 => witness797 | 4 => witness798 | 5 => witness799 | 6 => witness800 | _ => witness801

def witnessTreeLRRLRRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeLRRLRRLL i else witnessTreeLRRLRRLR (i - 7)

def witnessTreeLRRLRRRL (i : Nat) : OrbitWitness := match i with | 0 => witness802 | 1 => witness803 | 2 => witness804 | 3 => witness805 | 4 => witness806 | 5 => witness807 | _ => witness808

def witnessTreeLRRLRRRR (i : Nat) : OrbitWitness := match i with | 0 => witness809 | 1 => witness810 | 2 => witness811 | 3 => witness812 | 4 => witness813 | 5 => witness814 | 6 => witness815 | _ => witness816

def witnessTreeLRRLRRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeLRRLRRRL i else witnessTreeLRRLRRRR (i - 7)

def witnessTreeLRRLRR (i : Nat) : OrbitWitness := if i < 15 then witnessTreeLRRLRRL i else witnessTreeLRRLRRR (i - 15)

def witnessTreeLRRLR (i : Nat) : OrbitWitness := if i < 29 then witnessTreeLRRLRL i else witnessTreeLRRLRR (i - 29)

def witnessTreeLRRL (i : Nat) : OrbitWitness := if i < 58 then witnessTreeLRRLL i else witnessTreeLRRLR (i - 58)

def witnessTreeLRRRLLLL (i : Nat) : OrbitWitness := match i with | 0 => witness817 | 1 => witness818 | 2 => witness819 | 3 => witness820 | 4 => witness821 | 5 => witness822 | _ => witness823

def witnessTreeLRRRLLLR (i : Nat) : OrbitWitness := match i with | 0 => witness824 | 1 => witness825 | 2 => witness826 | 3 => witness827 | 4 => witness828 | 5 => witness829 | _ => witness830

def witnessTreeLRRRLLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeLRRRLLLL i else witnessTreeLRRRLLLR (i - 7)

def witnessTreeLRRRLLRL (i : Nat) : OrbitWitness := match i with | 0 => witness831 | 1 => witness832 | 2 => witness833 | 3 => witness834 | 4 => witness835 | 5 => witness836 | _ => witness837

def witnessTreeLRRRLLRR (i : Nat) : OrbitWitness := match i with | 0 => witness838 | 1 => witness839 | 2 => witness840 | 3 => witness841 | 4 => witness842 | 5 => witness843 | 6 => witness844 | _ => witness845

def witnessTreeLRRRLLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeLRRRLLRL i else witnessTreeLRRRLLRR (i - 7)

def witnessTreeLRRRLL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeLRRRLLL i else witnessTreeLRRRLLR (i - 14)

def witnessTreeLRRRLRLL (i : Nat) : OrbitWitness := match i with | 0 => witness846 | 1 => witness847 | 2 => witness848 | 3 => witness849 | 4 => witness850 | 5 => witness851 | _ => witness852

def witnessTreeLRRRLRLR (i : Nat) : OrbitWitness := match i with | 0 => witness853 | 1 => witness854 | 2 => witness855 | 3 => witness856 | 4 => witness857 | 5 => witness858 | _ => witness859

def witnessTreeLRRRLRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeLRRRLRLL i else witnessTreeLRRRLRLR (i - 7)

def witnessTreeLRRRLRRL (i : Nat) : OrbitWitness := match i with | 0 => witness860 | 1 => witness861 | 2 => witness862 | 3 => witness863 | 4 => witness864 | 5 => witness865 | _ => witness866

def witnessTreeLRRRLRRR (i : Nat) : OrbitWitness := match i with | 0 => witness867 | 1 => witness868 | 2 => witness869 | 3 => witness870 | 4 => witness871 | 5 => witness872 | 6 => witness873 | _ => witness874

def witnessTreeLRRRLRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeLRRRLRRL i else witnessTreeLRRRLRRR (i - 7)

def witnessTreeLRRRLR (i : Nat) : OrbitWitness := if i < 14 then witnessTreeLRRRLRL i else witnessTreeLRRRLRR (i - 14)

def witnessTreeLRRRL (i : Nat) : OrbitWitness := if i < 29 then witnessTreeLRRRLL i else witnessTreeLRRRLR (i - 29)

def witnessTreeLRRRRLLL (i : Nat) : OrbitWitness := match i with | 0 => witness875 | 1 => witness876 | 2 => witness877 | 3 => witness878 | 4 => witness879 | 5 => witness880 | _ => witness881

def witnessTreeLRRRRLLR (i : Nat) : OrbitWitness := match i with | 0 => witness882 | 1 => witness883 | 2 => witness884 | 3 => witness885 | 4 => witness886 | 5 => witness887 | _ => witness888

def witnessTreeLRRRRLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeLRRRRLLL i else witnessTreeLRRRRLLR (i - 7)

def witnessTreeLRRRRLRL (i : Nat) : OrbitWitness := match i with | 0 => witness889 | 1 => witness890 | 2 => witness891 | 3 => witness892 | 4 => witness893 | 5 => witness894 | _ => witness895

def witnessTreeLRRRRLRR (i : Nat) : OrbitWitness := match i with | 0 => witness896 | 1 => witness897 | 2 => witness898 | 3 => witness899 | 4 => witness900 | 5 => witness901 | 6 => witness902 | _ => witness903

def witnessTreeLRRRRLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeLRRRRLRL i else witnessTreeLRRRRLRR (i - 7)

def witnessTreeLRRRRL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeLRRRRLL i else witnessTreeLRRRRLR (i - 14)

def witnessTreeLRRRRRLL (i : Nat) : OrbitWitness := match i with | 0 => witness904 | 1 => witness905 | 2 => witness906 | 3 => witness907 | 4 => witness908 | 5 => witness909 | _ => witness910

def witnessTreeLRRRRRLR (i : Nat) : OrbitWitness := match i with | 0 => witness911 | 1 => witness912 | 2 => witness913 | 3 => witness914 | 4 => witness915 | 5 => witness916 | 6 => witness917 | _ => witness918

def witnessTreeLRRRRRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeLRRRRRLL i else witnessTreeLRRRRRLR (i - 7)

def witnessTreeLRRRRRRL (i : Nat) : OrbitWitness := match i with | 0 => witness919 | 1 => witness920 | 2 => witness921 | 3 => witness922 | 4 => witness923 | 5 => witness924 | _ => witness925

def witnessTreeLRRRRRRR (i : Nat) : OrbitWitness := match i with | 0 => witness926 | 1 => witness927 | 2 => witness928 | 3 => witness929 | 4 => witness930 | 5 => witness931 | 6 => witness932 | _ => witness933

def witnessTreeLRRRRRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeLRRRRRRL i else witnessTreeLRRRRRRR (i - 7)

def witnessTreeLRRRRR (i : Nat) : OrbitWitness := if i < 15 then witnessTreeLRRRRRL i else witnessTreeLRRRRRR (i - 15)

def witnessTreeLRRRR (i : Nat) : OrbitWitness := if i < 29 then witnessTreeLRRRRL i else witnessTreeLRRRRR (i - 29)

def witnessTreeLRRR (i : Nat) : OrbitWitness := if i < 58 then witnessTreeLRRRL i else witnessTreeLRRRR (i - 58)

def witnessTreeLRR (i : Nat) : OrbitWitness := if i < 117 then witnessTreeLRRL i else witnessTreeLRRR (i - 117)

def witnessTreeLR (i : Nat) : OrbitWitness := if i < 233 then witnessTreeLRL i else witnessTreeLRR (i - 233)

def witnessTreeL (i : Nat) : OrbitWitness := if i < 467 then witnessTreeLL i else witnessTreeLR (i - 467)

def witnessTreeRLLLLLLL (i : Nat) : OrbitWitness := match i with | 0 => witness934 | 1 => witness935 | 2 => witness936 | 3 => witness937 | 4 => witness938 | 5 => witness939 | _ => witness940

def witnessTreeRLLLLLLR (i : Nat) : OrbitWitness := match i with | 0 => witness941 | 1 => witness942 | 2 => witness943 | 3 => witness944 | 4 => witness945 | 5 => witness946 | _ => witness947

def witnessTreeRLLLLLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLLLLLLL i else witnessTreeRLLLLLLR (i - 7)

def witnessTreeRLLLLLRL (i : Nat) : OrbitWitness := match i with | 0 => witness948 | 1 => witness949 | 2 => witness950 | 3 => witness951 | 4 => witness952 | 5 => witness953 | _ => witness954

def witnessTreeRLLLLLRR (i : Nat) : OrbitWitness := match i with | 0 => witness955 | 1 => witness956 | 2 => witness957 | 3 => witness958 | 4 => witness959 | 5 => witness960 | 6 => witness961 | _ => witness962

def witnessTreeRLLLLLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLLLLLRL i else witnessTreeRLLLLLRR (i - 7)

def witnessTreeRLLLLL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRLLLLLL i else witnessTreeRLLLLLR (i - 14)

def witnessTreeRLLLLRLL (i : Nat) : OrbitWitness := match i with | 0 => witness963 | 1 => witness964 | 2 => witness965 | 3 => witness966 | 4 => witness967 | 5 => witness968 | _ => witness969

def witnessTreeRLLLLRLR (i : Nat) : OrbitWitness := match i with | 0 => witness970 | 1 => witness971 | 2 => witness972 | 3 => witness973 | 4 => witness974 | 5 => witness975 | _ => witness976

def witnessTreeRLLLLRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLLLLRLL i else witnessTreeRLLLLRLR (i - 7)

def witnessTreeRLLLLRRL (i : Nat) : OrbitWitness := match i with | 0 => witness977 | 1 => witness978 | 2 => witness979 | 3 => witness980 | 4 => witness981 | 5 => witness982 | _ => witness983

def witnessTreeRLLLLRRR (i : Nat) : OrbitWitness := match i with | 0 => witness984 | 1 => witness985 | 2 => witness986 | 3 => witness987 | 4 => witness988 | 5 => witness989 | 6 => witness990 | _ => witness991

def witnessTreeRLLLLRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLLLLRRL i else witnessTreeRLLLLRRR (i - 7)

def witnessTreeRLLLLR (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRLLLLRL i else witnessTreeRLLLLRR (i - 14)

def witnessTreeRLLLL (i : Nat) : OrbitWitness := if i < 29 then witnessTreeRLLLLL i else witnessTreeRLLLLR (i - 29)

def witnessTreeRLLLRLLL (i : Nat) : OrbitWitness := match i with | 0 => witness992 | 1 => witness993 | 2 => witness994 | 3 => witness995 | 4 => witness996 | 5 => witness997 | _ => witness998

def witnessTreeRLLLRLLR (i : Nat) : OrbitWitness := match i with | 0 => witness999 | 1 => witness1000 | 2 => witness1001 | 3 => witness1002 | 4 => witness1003 | 5 => witness1004 | _ => witness1005

def witnessTreeRLLLRLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLLLRLLL i else witnessTreeRLLLRLLR (i - 7)

def witnessTreeRLLLRLRL (i : Nat) : OrbitWitness := match i with | 0 => witness1006 | 1 => witness1007 | 2 => witness1008 | 3 => witness1009 | 4 => witness1010 | 5 => witness1011 | _ => witness1012

def witnessTreeRLLLRLRR (i : Nat) : OrbitWitness := match i with | 0 => witness1013 | 1 => witness1014 | 2 => witness1015 | 3 => witness1016 | 4 => witness1017 | 5 => witness1018 | 6 => witness1019 | _ => witness1020

def witnessTreeRLLLRLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLLLRLRL i else witnessTreeRLLLRLRR (i - 7)

def witnessTreeRLLLRL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRLLLRLL i else witnessTreeRLLLRLR (i - 14)

def witnessTreeRLLLRRLL (i : Nat) : OrbitWitness := match i with | 0 => witness1021 | 1 => witness1022 | 2 => witness1023 | 3 => witness1024 | 4 => witness1025 | 5 => witness1026 | _ => witness1027

def witnessTreeRLLLRRLR (i : Nat) : OrbitWitness := match i with | 0 => witness1028 | 1 => witness1029 | 2 => witness1030 | 3 => witness1031 | 4 => witness1032 | 5 => witness1033 | _ => witness1034

def witnessTreeRLLLRRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLLLRRLL i else witnessTreeRLLLRRLR (i - 7)

def witnessTreeRLLLRRRL (i : Nat) : OrbitWitness := match i with | 0 => witness1035 | 1 => witness1036 | 2 => witness1037 | 3 => witness1038 | 4 => witness1039 | 5 => witness1040 | _ => witness1041

def witnessTreeRLLLRRRR (i : Nat) : OrbitWitness := match i with | 0 => witness1042 | 1 => witness1043 | 2 => witness1044 | 3 => witness1045 | 4 => witness1046 | 5 => witness1047 | 6 => witness1048 | _ => witness1049

def witnessTreeRLLLRRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLLLRRRL i else witnessTreeRLLLRRRR (i - 7)

def witnessTreeRLLLRR (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRLLLRRL i else witnessTreeRLLLRRR (i - 14)

def witnessTreeRLLLR (i : Nat) : OrbitWitness := if i < 29 then witnessTreeRLLLRL i else witnessTreeRLLLRR (i - 29)

def witnessTreeRLLL (i : Nat) : OrbitWitness := if i < 58 then witnessTreeRLLLL i else witnessTreeRLLLR (i - 58)

def witnessTreeRLLRLLLL (i : Nat) : OrbitWitness := match i with | 0 => witness1050 | 1 => witness1051 | 2 => witness1052 | 3 => witness1053 | 4 => witness1054 | 5 => witness1055 | _ => witness1056

def witnessTreeRLLRLLLR (i : Nat) : OrbitWitness := match i with | 0 => witness1057 | 1 => witness1058 | 2 => witness1059 | 3 => witness1060 | 4 => witness1061 | 5 => witness1062 | _ => witness1063

def witnessTreeRLLRLLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLLRLLLL i else witnessTreeRLLRLLLR (i - 7)

def witnessTreeRLLRLLRL (i : Nat) : OrbitWitness := match i with | 0 => witness1064 | 1 => witness1065 | 2 => witness1066 | 3 => witness1067 | 4 => witness1068 | 5 => witness1069 | _ => witness1070

def witnessTreeRLLRLLRR (i : Nat) : OrbitWitness := match i with | 0 => witness1071 | 1 => witness1072 | 2 => witness1073 | 3 => witness1074 | 4 => witness1075 | 5 => witness1076 | 6 => witness1077 | _ => witness1078

def witnessTreeRLLRLLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLLRLLRL i else witnessTreeRLLRLLRR (i - 7)

def witnessTreeRLLRLL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRLLRLLL i else witnessTreeRLLRLLR (i - 14)

def witnessTreeRLLRLRLL (i : Nat) : OrbitWitness := match i with | 0 => witness1079 | 1 => witness1080 | 2 => witness1081 | 3 => witness1082 | 4 => witness1083 | 5 => witness1084 | _ => witness1085

def witnessTreeRLLRLRLR (i : Nat) : OrbitWitness := match i with | 0 => witness1086 | 1 => witness1087 | 2 => witness1088 | 3 => witness1089 | 4 => witness1090 | 5 => witness1091 | _ => witness1092

def witnessTreeRLLRLRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLLRLRLL i else witnessTreeRLLRLRLR (i - 7)

def witnessTreeRLLRLRRL (i : Nat) : OrbitWitness := match i with | 0 => witness1093 | 1 => witness1094 | 2 => witness1095 | 3 => witness1096 | 4 => witness1097 | 5 => witness1098 | _ => witness1099

def witnessTreeRLLRLRRR (i : Nat) : OrbitWitness := match i with | 0 => witness1100 | 1 => witness1101 | 2 => witness1102 | 3 => witness1103 | 4 => witness1104 | 5 => witness1105 | 6 => witness1106 | _ => witness1107

def witnessTreeRLLRLRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLLRLRRL i else witnessTreeRLLRLRRR (i - 7)

def witnessTreeRLLRLR (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRLLRLRL i else witnessTreeRLLRLRR (i - 14)

def witnessTreeRLLRL (i : Nat) : OrbitWitness := if i < 29 then witnessTreeRLLRLL i else witnessTreeRLLRLR (i - 29)

def witnessTreeRLLRRLLL (i : Nat) : OrbitWitness := match i with | 0 => witness1108 | 1 => witness1109 | 2 => witness1110 | 3 => witness1111 | 4 => witness1112 | 5 => witness1113 | _ => witness1114

def witnessTreeRLLRRLLR (i : Nat) : OrbitWitness := match i with | 0 => witness1115 | 1 => witness1116 | 2 => witness1117 | 3 => witness1118 | 4 => witness1119 | 5 => witness1120 | _ => witness1121

def witnessTreeRLLRRLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLLRRLLL i else witnessTreeRLLRRLLR (i - 7)

def witnessTreeRLLRRLRL (i : Nat) : OrbitWitness := match i with | 0 => witness1122 | 1 => witness1123 | 2 => witness1124 | 3 => witness1125 | 4 => witness1126 | 5 => witness1127 | _ => witness1128

def witnessTreeRLLRRLRR (i : Nat) : OrbitWitness := match i with | 0 => witness1129 | 1 => witness1130 | 2 => witness1131 | 3 => witness1132 | 4 => witness1133 | 5 => witness1134 | 6 => witness1135 | _ => witness1136

def witnessTreeRLLRRLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLLRRLRL i else witnessTreeRLLRRLRR (i - 7)

def witnessTreeRLLRRL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRLLRRLL i else witnessTreeRLLRRLR (i - 14)

def witnessTreeRLLRRRLL (i : Nat) : OrbitWitness := match i with | 0 => witness1137 | 1 => witness1138 | 2 => witness1139 | 3 => witness1140 | 4 => witness1141 | 5 => witness1142 | _ => witness1143

def witnessTreeRLLRRRLR (i : Nat) : OrbitWitness := match i with | 0 => witness1144 | 1 => witness1145 | 2 => witness1146 | 3 => witness1147 | 4 => witness1148 | 5 => witness1149 | 6 => witness1150 | _ => witness1151

def witnessTreeRLLRRRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLLRRRLL i else witnessTreeRLLRRRLR (i - 7)

def witnessTreeRLLRRRRL (i : Nat) : OrbitWitness := match i with | 0 => witness1152 | 1 => witness1153 | 2 => witness1154 | 3 => witness1155 | 4 => witness1156 | 5 => witness1157 | _ => witness1158

def witnessTreeRLLRRRRR (i : Nat) : OrbitWitness := match i with | 0 => witness1159 | 1 => witness1160 | 2 => witness1161 | 3 => witness1162 | 4 => witness1163 | 5 => witness1164 | 6 => witness1165 | _ => witness1166

def witnessTreeRLLRRRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLLRRRRL i else witnessTreeRLLRRRRR (i - 7)

def witnessTreeRLLRRR (i : Nat) : OrbitWitness := if i < 15 then witnessTreeRLLRRRL i else witnessTreeRLLRRRR (i - 15)

def witnessTreeRLLRR (i : Nat) : OrbitWitness := if i < 29 then witnessTreeRLLRRL i else witnessTreeRLLRRR (i - 29)

def witnessTreeRLLR (i : Nat) : OrbitWitness := if i < 58 then witnessTreeRLLRL i else witnessTreeRLLRR (i - 58)

def witnessTreeRLL (i : Nat) : OrbitWitness := if i < 116 then witnessTreeRLLL i else witnessTreeRLLR (i - 116)

def witnessTreeRLRLLLLL (i : Nat) : OrbitWitness := match i with | 0 => witness1167 | 1 => witness1168 | 2 => witness1169 | 3 => witness1170 | 4 => witness1171 | 5 => witness1172 | _ => witness1173

def witnessTreeRLRLLLLR (i : Nat) : OrbitWitness := match i with | 0 => witness1174 | 1 => witness1175 | 2 => witness1176 | 3 => witness1177 | 4 => witness1178 | 5 => witness1179 | _ => witness1180

def witnessTreeRLRLLLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLRLLLLL i else witnessTreeRLRLLLLR (i - 7)

def witnessTreeRLRLLLRL (i : Nat) : OrbitWitness := match i with | 0 => witness1181 | 1 => witness1182 | 2 => witness1183 | 3 => witness1184 | 4 => witness1185 | 5 => witness1186 | _ => witness1187

def witnessTreeRLRLLLRR (i : Nat) : OrbitWitness := match i with | 0 => witness1188 | 1 => witness1189 | 2 => witness1190 | 3 => witness1191 | 4 => witness1192 | 5 => witness1193 | 6 => witness1194 | _ => witness1195

def witnessTreeRLRLLLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLRLLLRL i else witnessTreeRLRLLLRR (i - 7)

def witnessTreeRLRLLL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRLRLLLL i else witnessTreeRLRLLLR (i - 14)

def witnessTreeRLRLLRLL (i : Nat) : OrbitWitness := match i with | 0 => witness1196 | 1 => witness1197 | 2 => witness1198 | 3 => witness1199 | 4 => witness1200 | 5 => witness1201 | _ => witness1202

def witnessTreeRLRLLRLR (i : Nat) : OrbitWitness := match i with | 0 => witness1203 | 1 => witness1204 | 2 => witness1205 | 3 => witness1206 | 4 => witness1207 | 5 => witness1208 | _ => witness1209

def witnessTreeRLRLLRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLRLLRLL i else witnessTreeRLRLLRLR (i - 7)

def witnessTreeRLRLLRRL (i : Nat) : OrbitWitness := match i with | 0 => witness1210 | 1 => witness1211 | 2 => witness1212 | 3 => witness1213 | 4 => witness1214 | 5 => witness1215 | _ => witness1216

def witnessTreeRLRLLRRR (i : Nat) : OrbitWitness := match i with | 0 => witness1217 | 1 => witness1218 | 2 => witness1219 | 3 => witness1220 | 4 => witness1221 | 5 => witness1222 | 6 => witness1223 | _ => witness1224

def witnessTreeRLRLLRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLRLLRRL i else witnessTreeRLRLLRRR (i - 7)

def witnessTreeRLRLLR (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRLRLLRL i else witnessTreeRLRLLRR (i - 14)

def witnessTreeRLRLL (i : Nat) : OrbitWitness := if i < 29 then witnessTreeRLRLLL i else witnessTreeRLRLLR (i - 29)

def witnessTreeRLRLRLLL (i : Nat) : OrbitWitness := match i with | 0 => witness1225 | 1 => witness1226 | 2 => witness1227 | 3 => witness1228 | 4 => witness1229 | 5 => witness1230 | _ => witness1231

def witnessTreeRLRLRLLR (i : Nat) : OrbitWitness := match i with | 0 => witness1232 | 1 => witness1233 | 2 => witness1234 | 3 => witness1235 | 4 => witness1236 | 5 => witness1237 | _ => witness1238

def witnessTreeRLRLRLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLRLRLLL i else witnessTreeRLRLRLLR (i - 7)

def witnessTreeRLRLRLRL (i : Nat) : OrbitWitness := match i with | 0 => witness1239 | 1 => witness1240 | 2 => witness1241 | 3 => witness1242 | 4 => witness1243 | 5 => witness1244 | _ => witness1245

def witnessTreeRLRLRLRR (i : Nat) : OrbitWitness := match i with | 0 => witness1246 | 1 => witness1247 | 2 => witness1248 | 3 => witness1249 | 4 => witness1250 | 5 => witness1251 | 6 => witness1252 | _ => witness1253

def witnessTreeRLRLRLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLRLRLRL i else witnessTreeRLRLRLRR (i - 7)

def witnessTreeRLRLRL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRLRLRLL i else witnessTreeRLRLRLR (i - 14)

def witnessTreeRLRLRRLL (i : Nat) : OrbitWitness := match i with | 0 => witness1254 | 1 => witness1255 | 2 => witness1256 | 3 => witness1257 | 4 => witness1258 | 5 => witness1259 | _ => witness1260

def witnessTreeRLRLRRLR (i : Nat) : OrbitWitness := match i with | 0 => witness1261 | 1 => witness1262 | 2 => witness1263 | 3 => witness1264 | 4 => witness1265 | 5 => witness1266 | 6 => witness1267 | _ => witness1268

def witnessTreeRLRLRRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLRLRRLL i else witnessTreeRLRLRRLR (i - 7)

def witnessTreeRLRLRRRL (i : Nat) : OrbitWitness := match i with | 0 => witness1269 | 1 => witness1270 | 2 => witness1271 | 3 => witness1272 | 4 => witness1273 | 5 => witness1274 | _ => witness1275

def witnessTreeRLRLRRRR (i : Nat) : OrbitWitness := match i with | 0 => witness1276 | 1 => witness1277 | 2 => witness1278 | 3 => witness1279 | 4 => witness1280 | 5 => witness1281 | 6 => witness1282 | _ => witness1283

def witnessTreeRLRLRRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLRLRRRL i else witnessTreeRLRLRRRR (i - 7)

def witnessTreeRLRLRR (i : Nat) : OrbitWitness := if i < 15 then witnessTreeRLRLRRL i else witnessTreeRLRLRRR (i - 15)

def witnessTreeRLRLR (i : Nat) : OrbitWitness := if i < 29 then witnessTreeRLRLRL i else witnessTreeRLRLRR (i - 29)

def witnessTreeRLRL (i : Nat) : OrbitWitness := if i < 58 then witnessTreeRLRLL i else witnessTreeRLRLR (i - 58)

def witnessTreeRLRRLLLL (i : Nat) : OrbitWitness := match i with | 0 => witness1284 | 1 => witness1285 | 2 => witness1286 | 3 => witness1287 | 4 => witness1288 | 5 => witness1289 | _ => witness1290

def witnessTreeRLRRLLLR (i : Nat) : OrbitWitness := match i with | 0 => witness1291 | 1 => witness1292 | 2 => witness1293 | 3 => witness1294 | 4 => witness1295 | 5 => witness1296 | _ => witness1297

def witnessTreeRLRRLLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLRRLLLL i else witnessTreeRLRRLLLR (i - 7)

def witnessTreeRLRRLLRL (i : Nat) : OrbitWitness := match i with | 0 => witness1298 | 1 => witness1299 | 2 => witness1300 | 3 => witness1301 | 4 => witness1302 | 5 => witness1303 | _ => witness1304

def witnessTreeRLRRLLRR (i : Nat) : OrbitWitness := match i with | 0 => witness1305 | 1 => witness1306 | 2 => witness1307 | 3 => witness1308 | 4 => witness1309 | 5 => witness1310 | 6 => witness1311 | _ => witness1312

def witnessTreeRLRRLLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLRRLLRL i else witnessTreeRLRRLLRR (i - 7)

def witnessTreeRLRRLL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRLRRLLL i else witnessTreeRLRRLLR (i - 14)

def witnessTreeRLRRLRLL (i : Nat) : OrbitWitness := match i with | 0 => witness1313 | 1 => witness1314 | 2 => witness1315 | 3 => witness1316 | 4 => witness1317 | 5 => witness1318 | _ => witness1319

def witnessTreeRLRRLRLR (i : Nat) : OrbitWitness := match i with | 0 => witness1320 | 1 => witness1321 | 2 => witness1322 | 3 => witness1323 | 4 => witness1324 | 5 => witness1325 | _ => witness1326

def witnessTreeRLRRLRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLRRLRLL i else witnessTreeRLRRLRLR (i - 7)

def witnessTreeRLRRLRRL (i : Nat) : OrbitWitness := match i with | 0 => witness1327 | 1 => witness1328 | 2 => witness1329 | 3 => witness1330 | 4 => witness1331 | 5 => witness1332 | _ => witness1333

def witnessTreeRLRRLRRR (i : Nat) : OrbitWitness := match i with | 0 => witness1334 | 1 => witness1335 | 2 => witness1336 | 3 => witness1337 | 4 => witness1338 | 5 => witness1339 | 6 => witness1340 | _ => witness1341

def witnessTreeRLRRLRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLRRLRRL i else witnessTreeRLRRLRRR (i - 7)

def witnessTreeRLRRLR (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRLRRLRL i else witnessTreeRLRRLRR (i - 14)

def witnessTreeRLRRL (i : Nat) : OrbitWitness := if i < 29 then witnessTreeRLRRLL i else witnessTreeRLRRLR (i - 29)

def witnessTreeRLRRRLLL (i : Nat) : OrbitWitness := match i with | 0 => witness1342 | 1 => witness1343 | 2 => witness1344 | 3 => witness1345 | 4 => witness1346 | 5 => witness1347 | _ => witness1348

def witnessTreeRLRRRLLR (i : Nat) : OrbitWitness := match i with | 0 => witness1349 | 1 => witness1350 | 2 => witness1351 | 3 => witness1352 | 4 => witness1353 | 5 => witness1354 | _ => witness1355

def witnessTreeRLRRRLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLRRRLLL i else witnessTreeRLRRRLLR (i - 7)

def witnessTreeRLRRRLRL (i : Nat) : OrbitWitness := match i with | 0 => witness1356 | 1 => witness1357 | 2 => witness1358 | 3 => witness1359 | 4 => witness1360 | 5 => witness1361 | _ => witness1362

def witnessTreeRLRRRLRR (i : Nat) : OrbitWitness := match i with | 0 => witness1363 | 1 => witness1364 | 2 => witness1365 | 3 => witness1366 | 4 => witness1367 | 5 => witness1368 | 6 => witness1369 | _ => witness1370

def witnessTreeRLRRRLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLRRRLRL i else witnessTreeRLRRRLRR (i - 7)

def witnessTreeRLRRRL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRLRRRLL i else witnessTreeRLRRRLR (i - 14)

def witnessTreeRLRRRRLL (i : Nat) : OrbitWitness := match i with | 0 => witness1371 | 1 => witness1372 | 2 => witness1373 | 3 => witness1374 | 4 => witness1375 | 5 => witness1376 | _ => witness1377

def witnessTreeRLRRRRLR (i : Nat) : OrbitWitness := match i with | 0 => witness1378 | 1 => witness1379 | 2 => witness1380 | 3 => witness1381 | 4 => witness1382 | 5 => witness1383 | 6 => witness1384 | _ => witness1385

def witnessTreeRLRRRRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLRRRRLL i else witnessTreeRLRRRRLR (i - 7)

def witnessTreeRLRRRRRL (i : Nat) : OrbitWitness := match i with | 0 => witness1386 | 1 => witness1387 | 2 => witness1388 | 3 => witness1389 | 4 => witness1390 | 5 => witness1391 | _ => witness1392

def witnessTreeRLRRRRRR (i : Nat) : OrbitWitness := match i with | 0 => witness1393 | 1 => witness1394 | 2 => witness1395 | 3 => witness1396 | 4 => witness1397 | 5 => witness1398 | 6 => witness1399 | _ => witness1400

def witnessTreeRLRRRRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRLRRRRRL i else witnessTreeRLRRRRRR (i - 7)

def witnessTreeRLRRRR (i : Nat) : OrbitWitness := if i < 15 then witnessTreeRLRRRRL i else witnessTreeRLRRRRR (i - 15)

def witnessTreeRLRRR (i : Nat) : OrbitWitness := if i < 29 then witnessTreeRLRRRL i else witnessTreeRLRRRR (i - 29)

def witnessTreeRLRR (i : Nat) : OrbitWitness := if i < 58 then witnessTreeRLRRL i else witnessTreeRLRRR (i - 58)

def witnessTreeRLR (i : Nat) : OrbitWitness := if i < 117 then witnessTreeRLRL i else witnessTreeRLRR (i - 117)

def witnessTreeRL (i : Nat) : OrbitWitness := if i < 233 then witnessTreeRLL i else witnessTreeRLR (i - 233)

def witnessTreeRRLLLLLL (i : Nat) : OrbitWitness := match i with | 0 => witness1401 | 1 => witness1402 | 2 => witness1403 | 3 => witness1404 | 4 => witness1405 | 5 => witness1406 | _ => witness1407

def witnessTreeRRLLLLLR (i : Nat) : OrbitWitness := match i with | 0 => witness1408 | 1 => witness1409 | 2 => witness1410 | 3 => witness1411 | 4 => witness1412 | 5 => witness1413 | _ => witness1414

def witnessTreeRRLLLLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRLLLLLL i else witnessTreeRRLLLLLR (i - 7)

def witnessTreeRRLLLLRL (i : Nat) : OrbitWitness := match i with | 0 => witness1415 | 1 => witness1416 | 2 => witness1417 | 3 => witness1418 | 4 => witness1419 | 5 => witness1420 | _ => witness1421

def witnessTreeRRLLLLRR (i : Nat) : OrbitWitness := match i with | 0 => witness1422 | 1 => witness1423 | 2 => witness1424 | 3 => witness1425 | 4 => witness1426 | 5 => witness1427 | 6 => witness1428 | _ => witness1429

def witnessTreeRRLLLLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRLLLLRL i else witnessTreeRRLLLLRR (i - 7)

def witnessTreeRRLLLL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRRLLLLL i else witnessTreeRRLLLLR (i - 14)

def witnessTreeRRLLLRLL (i : Nat) : OrbitWitness := match i with | 0 => witness1430 | 1 => witness1431 | 2 => witness1432 | 3 => witness1433 | 4 => witness1434 | 5 => witness1435 | _ => witness1436

def witnessTreeRRLLLRLR (i : Nat) : OrbitWitness := match i with | 0 => witness1437 | 1 => witness1438 | 2 => witness1439 | 3 => witness1440 | 4 => witness1441 | 5 => witness1442 | _ => witness1443

def witnessTreeRRLLLRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRLLLRLL i else witnessTreeRRLLLRLR (i - 7)

def witnessTreeRRLLLRRL (i : Nat) : OrbitWitness := match i with | 0 => witness1444 | 1 => witness1445 | 2 => witness1446 | 3 => witness1447 | 4 => witness1448 | 5 => witness1449 | _ => witness1450

def witnessTreeRRLLLRRR (i : Nat) : OrbitWitness := match i with | 0 => witness1451 | 1 => witness1452 | 2 => witness1453 | 3 => witness1454 | 4 => witness1455 | 5 => witness1456 | 6 => witness1457 | _ => witness1458

def witnessTreeRRLLLRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRLLLRRL i else witnessTreeRRLLLRRR (i - 7)

def witnessTreeRRLLLR (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRRLLLRL i else witnessTreeRRLLLRR (i - 14)

def witnessTreeRRLLL (i : Nat) : OrbitWitness := if i < 29 then witnessTreeRRLLLL i else witnessTreeRRLLLR (i - 29)

def witnessTreeRRLLRLLL (i : Nat) : OrbitWitness := match i with | 0 => witness1459 | 1 => witness1460 | 2 => witness1461 | 3 => witness1462 | 4 => witness1463 | 5 => witness1464 | _ => witness1465

def witnessTreeRRLLRLLR (i : Nat) : OrbitWitness := match i with | 0 => witness1466 | 1 => witness1467 | 2 => witness1468 | 3 => witness1469 | 4 => witness1470 | 5 => witness1471 | _ => witness1472

def witnessTreeRRLLRLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRLLRLLL i else witnessTreeRRLLRLLR (i - 7)

def witnessTreeRRLLRLRL (i : Nat) : OrbitWitness := match i with | 0 => witness1473 | 1 => witness1474 | 2 => witness1475 | 3 => witness1476 | 4 => witness1477 | 5 => witness1478 | _ => witness1479

def witnessTreeRRLLRLRR (i : Nat) : OrbitWitness := match i with | 0 => witness1480 | 1 => witness1481 | 2 => witness1482 | 3 => witness1483 | 4 => witness1484 | 5 => witness1485 | 6 => witness1486 | _ => witness1487

def witnessTreeRRLLRLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRLLRLRL i else witnessTreeRRLLRLRR (i - 7)

def witnessTreeRRLLRL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRRLLRLL i else witnessTreeRRLLRLR (i - 14)

def witnessTreeRRLLRRLL (i : Nat) : OrbitWitness := match i with | 0 => witness1488 | 1 => witness1489 | 2 => witness1490 | 3 => witness1491 | 4 => witness1492 | 5 => witness1493 | _ => witness1494

def witnessTreeRRLLRRLR (i : Nat) : OrbitWitness := match i with | 0 => witness1495 | 1 => witness1496 | 2 => witness1497 | 3 => witness1498 | 4 => witness1499 | 5 => witness1500 | _ => witness1501

def witnessTreeRRLLRRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRLLRRLL i else witnessTreeRRLLRRLR (i - 7)

def witnessTreeRRLLRRRL (i : Nat) : OrbitWitness := match i with | 0 => witness1502 | 1 => witness1503 | 2 => witness1504 | 3 => witness1505 | 4 => witness1506 | 5 => witness1507 | _ => witness1508

def witnessTreeRRLLRRRR (i : Nat) : OrbitWitness := match i with | 0 => witness1509 | 1 => witness1510 | 2 => witness1511 | 3 => witness1512 | 4 => witness1513 | 5 => witness1514 | 6 => witness1515 | _ => witness1516

def witnessTreeRRLLRRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRLLRRRL i else witnessTreeRRLLRRRR (i - 7)

def witnessTreeRRLLRR (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRRLLRRL i else witnessTreeRRLLRRR (i - 14)

def witnessTreeRRLLR (i : Nat) : OrbitWitness := if i < 29 then witnessTreeRRLLRL i else witnessTreeRRLLRR (i - 29)

def witnessTreeRRLL (i : Nat) : OrbitWitness := if i < 58 then witnessTreeRRLLL i else witnessTreeRRLLR (i - 58)

def witnessTreeRRLRLLLL (i : Nat) : OrbitWitness := match i with | 0 => witness1517 | 1 => witness1518 | 2 => witness1519 | 3 => witness1520 | 4 => witness1521 | 5 => witness1522 | _ => witness1523

def witnessTreeRRLRLLLR (i : Nat) : OrbitWitness := match i with | 0 => witness1524 | 1 => witness1525 | 2 => witness1526 | 3 => witness1527 | 4 => witness1528 | 5 => witness1529 | _ => witness1530

def witnessTreeRRLRLLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRLRLLLL i else witnessTreeRRLRLLLR (i - 7)

def witnessTreeRRLRLLRL (i : Nat) : OrbitWitness := match i with | 0 => witness1531 | 1 => witness1532 | 2 => witness1533 | 3 => witness1534 | 4 => witness1535 | 5 => witness1536 | _ => witness1537

def witnessTreeRRLRLLRR (i : Nat) : OrbitWitness := match i with | 0 => witness1538 | 1 => witness1539 | 2 => witness1540 | 3 => witness1541 | 4 => witness1542 | 5 => witness1543 | 6 => witness1544 | _ => witness1545

def witnessTreeRRLRLLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRLRLLRL i else witnessTreeRRLRLLRR (i - 7)

def witnessTreeRRLRLL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRRLRLLL i else witnessTreeRRLRLLR (i - 14)

def witnessTreeRRLRLRLL (i : Nat) : OrbitWitness := match i with | 0 => witness1546 | 1 => witness1547 | 2 => witness1548 | 3 => witness1549 | 4 => witness1550 | 5 => witness1551 | _ => witness1552

def witnessTreeRRLRLRLR (i : Nat) : OrbitWitness := match i with | 0 => witness1553 | 1 => witness1554 | 2 => witness1555 | 3 => witness1556 | 4 => witness1557 | 5 => witness1558 | _ => witness1559

def witnessTreeRRLRLRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRLRLRLL i else witnessTreeRRLRLRLR (i - 7)

def witnessTreeRRLRLRRL (i : Nat) : OrbitWitness := match i with | 0 => witness1560 | 1 => witness1561 | 2 => witness1562 | 3 => witness1563 | 4 => witness1564 | 5 => witness1565 | _ => witness1566

def witnessTreeRRLRLRRR (i : Nat) : OrbitWitness := match i with | 0 => witness1567 | 1 => witness1568 | 2 => witness1569 | 3 => witness1570 | 4 => witness1571 | 5 => witness1572 | 6 => witness1573 | _ => witness1574

def witnessTreeRRLRLRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRLRLRRL i else witnessTreeRRLRLRRR (i - 7)

def witnessTreeRRLRLR (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRRLRLRL i else witnessTreeRRLRLRR (i - 14)

def witnessTreeRRLRL (i : Nat) : OrbitWitness := if i < 29 then witnessTreeRRLRLL i else witnessTreeRRLRLR (i - 29)

def witnessTreeRRLRRLLL (i : Nat) : OrbitWitness := match i with | 0 => witness1575 | 1 => witness1576 | 2 => witness1577 | 3 => witness1578 | 4 => witness1579 | 5 => witness1580 | _ => witness1581

def witnessTreeRRLRRLLR (i : Nat) : OrbitWitness := match i with | 0 => witness1582 | 1 => witness1583 | 2 => witness1584 | 3 => witness1585 | 4 => witness1586 | 5 => witness1587 | _ => witness1588

def witnessTreeRRLRRLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRLRRLLL i else witnessTreeRRLRRLLR (i - 7)

def witnessTreeRRLRRLRL (i : Nat) : OrbitWitness := match i with | 0 => witness1589 | 1 => witness1590 | 2 => witness1591 | 3 => witness1592 | 4 => witness1593 | 5 => witness1594 | _ => witness1595

def witnessTreeRRLRRLRR (i : Nat) : OrbitWitness := match i with | 0 => witness1596 | 1 => witness1597 | 2 => witness1598 | 3 => witness1599 | 4 => witness1600 | 5 => witness1601 | 6 => witness1602 | _ => witness1603

def witnessTreeRRLRRLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRLRRLRL i else witnessTreeRRLRRLRR (i - 7)

def witnessTreeRRLRRL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRRLRRLL i else witnessTreeRRLRRLR (i - 14)

def witnessTreeRRLRRRLL (i : Nat) : OrbitWitness := match i with | 0 => witness1604 | 1 => witness1605 | 2 => witness1606 | 3 => witness1607 | 4 => witness1608 | 5 => witness1609 | _ => witness1610

def witnessTreeRRLRRRLR (i : Nat) : OrbitWitness := match i with | 0 => witness1611 | 1 => witness1612 | 2 => witness1613 | 3 => witness1614 | 4 => witness1615 | 5 => witness1616 | 6 => witness1617 | _ => witness1618

def witnessTreeRRLRRRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRLRRRLL i else witnessTreeRRLRRRLR (i - 7)

def witnessTreeRRLRRRRL (i : Nat) : OrbitWitness := match i with | 0 => witness1619 | 1 => witness1620 | 2 => witness1621 | 3 => witness1622 | 4 => witness1623 | 5 => witness1624 | _ => witness1625

def witnessTreeRRLRRRRR (i : Nat) : OrbitWitness := match i with | 0 => witness1626 | 1 => witness1627 | 2 => witness1628 | 3 => witness1629 | 4 => witness1630 | 5 => witness1631 | 6 => witness1632 | _ => witness1633

def witnessTreeRRLRRRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRLRRRRL i else witnessTreeRRLRRRRR (i - 7)

def witnessTreeRRLRRR (i : Nat) : OrbitWitness := if i < 15 then witnessTreeRRLRRRL i else witnessTreeRRLRRRR (i - 15)

def witnessTreeRRLRR (i : Nat) : OrbitWitness := if i < 29 then witnessTreeRRLRRL i else witnessTreeRRLRRR (i - 29)

def witnessTreeRRLR (i : Nat) : OrbitWitness := if i < 58 then witnessTreeRRLRL i else witnessTreeRRLRR (i - 58)

def witnessTreeRRL (i : Nat) : OrbitWitness := if i < 116 then witnessTreeRRLL i else witnessTreeRRLR (i - 116)

def witnessTreeRRRLLLLL (i : Nat) : OrbitWitness := match i with | 0 => witness1634 | 1 => witness1635 | 2 => witness1636 | 3 => witness1637 | 4 => witness1638 | 5 => witness1639 | _ => witness1640

def witnessTreeRRRLLLLR (i : Nat) : OrbitWitness := match i with | 0 => witness1641 | 1 => witness1642 | 2 => witness1643 | 3 => witness1644 | 4 => witness1645 | 5 => witness1646 | _ => witness1647

def witnessTreeRRRLLLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRRLLLLL i else witnessTreeRRRLLLLR (i - 7)

def witnessTreeRRRLLLRL (i : Nat) : OrbitWitness := match i with | 0 => witness1648 | 1 => witness1649 | 2 => witness1650 | 3 => witness1651 | 4 => witness1652 | 5 => witness1653 | _ => witness1654

def witnessTreeRRRLLLRR (i : Nat) : OrbitWitness := match i with | 0 => witness1655 | 1 => witness1656 | 2 => witness1657 | 3 => witness1658 | 4 => witness1659 | 5 => witness1660 | 6 => witness1661 | _ => witness1662

def witnessTreeRRRLLLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRRLLLRL i else witnessTreeRRRLLLRR (i - 7)

def witnessTreeRRRLLL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRRRLLLL i else witnessTreeRRRLLLR (i - 14)

def witnessTreeRRRLLRLL (i : Nat) : OrbitWitness := match i with | 0 => witness1663 | 1 => witness1664 | 2 => witness1665 | 3 => witness1666 | 4 => witness1667 | 5 => witness1668 | _ => witness1669

def witnessTreeRRRLLRLR (i : Nat) : OrbitWitness := match i with | 0 => witness1670 | 1 => witness1671 | 2 => witness1672 | 3 => witness1673 | 4 => witness1674 | 5 => witness1675 | _ => witness1676

def witnessTreeRRRLLRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRRLLRLL i else witnessTreeRRRLLRLR (i - 7)

def witnessTreeRRRLLRRL (i : Nat) : OrbitWitness := match i with | 0 => witness1677 | 1 => witness1678 | 2 => witness1679 | 3 => witness1680 | 4 => witness1681 | 5 => witness1682 | _ => witness1683

def witnessTreeRRRLLRRR (i : Nat) : OrbitWitness := match i with | 0 => witness1684 | 1 => witness1685 | 2 => witness1686 | 3 => witness1687 | 4 => witness1688 | 5 => witness1689 | 6 => witness1690 | _ => witness1691

def witnessTreeRRRLLRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRRLLRRL i else witnessTreeRRRLLRRR (i - 7)

def witnessTreeRRRLLR (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRRRLLRL i else witnessTreeRRRLLRR (i - 14)

def witnessTreeRRRLL (i : Nat) : OrbitWitness := if i < 29 then witnessTreeRRRLLL i else witnessTreeRRRLLR (i - 29)

def witnessTreeRRRLRLLL (i : Nat) : OrbitWitness := match i with | 0 => witness1692 | 1 => witness1693 | 2 => witness1694 | 3 => witness1695 | 4 => witness1696 | 5 => witness1697 | _ => witness1698

def witnessTreeRRRLRLLR (i : Nat) : OrbitWitness := match i with | 0 => witness1699 | 1 => witness1700 | 2 => witness1701 | 3 => witness1702 | 4 => witness1703 | 5 => witness1704 | _ => witness1705

def witnessTreeRRRLRLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRRLRLLL i else witnessTreeRRRLRLLR (i - 7)

def witnessTreeRRRLRLRL (i : Nat) : OrbitWitness := match i with | 0 => witness1706 | 1 => witness1707 | 2 => witness1708 | 3 => witness1709 | 4 => witness1710 | 5 => witness1711 | _ => witness1712

def witnessTreeRRRLRLRR (i : Nat) : OrbitWitness := match i with | 0 => witness1713 | 1 => witness1714 | 2 => witness1715 | 3 => witness1716 | 4 => witness1717 | 5 => witness1718 | 6 => witness1719 | _ => witness1720

def witnessTreeRRRLRLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRRLRLRL i else witnessTreeRRRLRLRR (i - 7)

def witnessTreeRRRLRL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRRRLRLL i else witnessTreeRRRLRLR (i - 14)

def witnessTreeRRRLRRLL (i : Nat) : OrbitWitness := match i with | 0 => witness1721 | 1 => witness1722 | 2 => witness1723 | 3 => witness1724 | 4 => witness1725 | 5 => witness1726 | _ => witness1727

def witnessTreeRRRLRRLR (i : Nat) : OrbitWitness := match i with | 0 => witness1728 | 1 => witness1729 | 2 => witness1730 | 3 => witness1731 | 4 => witness1732 | 5 => witness1733 | 6 => witness1734 | _ => witness1735

def witnessTreeRRRLRRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRRLRRLL i else witnessTreeRRRLRRLR (i - 7)

def witnessTreeRRRLRRRL (i : Nat) : OrbitWitness := match i with | 0 => witness1736 | 1 => witness1737 | 2 => witness1738 | 3 => witness1739 | 4 => witness1740 | 5 => witness1741 | _ => witness1742

def witnessTreeRRRLRRRR (i : Nat) : OrbitWitness := match i with | 0 => witness1743 | 1 => witness1744 | 2 => witness1745 | 3 => witness1746 | 4 => witness1747 | 5 => witness1748 | 6 => witness1749 | _ => witness1750

def witnessTreeRRRLRRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRRLRRRL i else witnessTreeRRRLRRRR (i - 7)

def witnessTreeRRRLRR (i : Nat) : OrbitWitness := if i < 15 then witnessTreeRRRLRRL i else witnessTreeRRRLRRR (i - 15)

def witnessTreeRRRLR (i : Nat) : OrbitWitness := if i < 29 then witnessTreeRRRLRL i else witnessTreeRRRLRR (i - 29)

def witnessTreeRRRL (i : Nat) : OrbitWitness := if i < 58 then witnessTreeRRRLL i else witnessTreeRRRLR (i - 58)

def witnessTreeRRRRLLLL (i : Nat) : OrbitWitness := match i with | 0 => witness1751 | 1 => witness1752 | 2 => witness1753 | 3 => witness1754 | 4 => witness1755 | 5 => witness1756 | _ => witness1757

def witnessTreeRRRRLLLR (i : Nat) : OrbitWitness := match i with | 0 => witness1758 | 1 => witness1759 | 2 => witness1760 | 3 => witness1761 | 4 => witness1762 | 5 => witness1763 | _ => witness1764

def witnessTreeRRRRLLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRRRLLLL i else witnessTreeRRRRLLLR (i - 7)

def witnessTreeRRRRLLRL (i : Nat) : OrbitWitness := match i with | 0 => witness1765 | 1 => witness1766 | 2 => witness1767 | 3 => witness1768 | 4 => witness1769 | 5 => witness1770 | _ => witness1771

def witnessTreeRRRRLLRR (i : Nat) : OrbitWitness := match i with | 0 => witness1772 | 1 => witness1773 | 2 => witness1774 | 3 => witness1775 | 4 => witness1776 | 5 => witness1777 | 6 => witness1778 | _ => witness1779

def witnessTreeRRRRLLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRRRLLRL i else witnessTreeRRRRLLRR (i - 7)

def witnessTreeRRRRLL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRRRRLLL i else witnessTreeRRRRLLR (i - 14)

def witnessTreeRRRRLRLL (i : Nat) : OrbitWitness := match i with | 0 => witness1780 | 1 => witness1781 | 2 => witness1782 | 3 => witness1783 | 4 => witness1784 | 5 => witness1785 | _ => witness1786

def witnessTreeRRRRLRLR (i : Nat) : OrbitWitness := match i with | 0 => witness1787 | 1 => witness1788 | 2 => witness1789 | 3 => witness1790 | 4 => witness1791 | 5 => witness1792 | _ => witness1793

def witnessTreeRRRRLRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRRRLRLL i else witnessTreeRRRRLRLR (i - 7)

def witnessTreeRRRRLRRL (i : Nat) : OrbitWitness := match i with | 0 => witness1794 | 1 => witness1795 | 2 => witness1796 | 3 => witness1797 | 4 => witness1798 | 5 => witness1799 | _ => witness1800

def witnessTreeRRRRLRRR (i : Nat) : OrbitWitness := match i with | 0 => witness1801 | 1 => witness1802 | 2 => witness1803 | 3 => witness1804 | 4 => witness1805 | 5 => witness1806 | 6 => witness1807 | _ => witness1808

def witnessTreeRRRRLRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRRRLRRL i else witnessTreeRRRRLRRR (i - 7)

def witnessTreeRRRRLR (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRRRRLRL i else witnessTreeRRRRLRR (i - 14)

def witnessTreeRRRRL (i : Nat) : OrbitWitness := if i < 29 then witnessTreeRRRRLL i else witnessTreeRRRRLR (i - 29)

def witnessTreeRRRRRLLL (i : Nat) : OrbitWitness := match i with | 0 => witness1809 | 1 => witness1810 | 2 => witness1811 | 3 => witness1812 | 4 => witness1813 | 5 => witness1814 | _ => witness1815

def witnessTreeRRRRRLLR (i : Nat) : OrbitWitness := match i with | 0 => witness1816 | 1 => witness1817 | 2 => witness1818 | 3 => witness1819 | 4 => witness1820 | 5 => witness1821 | _ => witness1822

def witnessTreeRRRRRLL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRRRRLLL i else witnessTreeRRRRRLLR (i - 7)

def witnessTreeRRRRRLRL (i : Nat) : OrbitWitness := match i with | 0 => witness1823 | 1 => witness1824 | 2 => witness1825 | 3 => witness1826 | 4 => witness1827 | 5 => witness1828 | _ => witness1829

def witnessTreeRRRRRLRR (i : Nat) : OrbitWitness := match i with | 0 => witness1830 | 1 => witness1831 | 2 => witness1832 | 3 => witness1833 | 4 => witness1834 | 5 => witness1835 | 6 => witness1836 | _ => witness1837

def witnessTreeRRRRRLR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRRRRLRL i else witnessTreeRRRRRLRR (i - 7)

def witnessTreeRRRRRL (i : Nat) : OrbitWitness := if i < 14 then witnessTreeRRRRRLL i else witnessTreeRRRRRLR (i - 14)

def witnessTreeRRRRRRLL (i : Nat) : OrbitWitness := match i with | 0 => witness1838 | 1 => witness1839 | 2 => witness1840 | 3 => witness1841 | 4 => witness1842 | 5 => witness1843 | _ => witness1844

def witnessTreeRRRRRRLR (i : Nat) : OrbitWitness := match i with | 0 => witness1845 | 1 => witness1846 | 2 => witness1847 | 3 => witness1848 | 4 => witness1849 | 5 => witness1850 | 6 => witness1851 | _ => witness1852

def witnessTreeRRRRRRL (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRRRRRLL i else witnessTreeRRRRRRLR (i - 7)

def witnessTreeRRRRRRRL (i : Nat) : OrbitWitness := match i with | 0 => witness1853 | 1 => witness1854 | 2 => witness1855 | 3 => witness1856 | 4 => witness1857 | 5 => witness1858 | _ => witness1859

def witnessTreeRRRRRRRR (i : Nat) : OrbitWitness := match i with | 0 => witness1860 | 1 => witness1861 | 2 => witness1862 | 3 => witness1863 | 4 => witness1864 | 5 => witness1865 | 6 => witness1866 | _ => witness1867

def witnessTreeRRRRRRR (i : Nat) : OrbitWitness := if i < 7 then witnessTreeRRRRRRRL i else witnessTreeRRRRRRRR (i - 7)

def witnessTreeRRRRRR (i : Nat) : OrbitWitness := if i < 15 then witnessTreeRRRRRRL i else witnessTreeRRRRRRR (i - 15)

def witnessTreeRRRRR (i : Nat) : OrbitWitness := if i < 29 then witnessTreeRRRRRL i else witnessTreeRRRRRR (i - 29)

def witnessTreeRRRR (i : Nat) : OrbitWitness := if i < 58 then witnessTreeRRRRL i else witnessTreeRRRRR (i - 58)

def witnessTreeRRR (i : Nat) : OrbitWitness := if i < 117 then witnessTreeRRRL i else witnessTreeRRRR (i - 117)

def witnessTreeRR (i : Nat) : OrbitWitness := if i < 233 then witnessTreeRRL i else witnessTreeRRR (i - 233)

def witnessTreeR (i : Nat) : OrbitWitness := if i < 467 then witnessTreeRL i else witnessTreeRR (i - 467)

def witnessTree (i : Nat) : OrbitWitness := if i < 934 then witnessTreeL i else witnessTreeR (i - 934)

end Paper2.Certificates.Q6.Coverage
