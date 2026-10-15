import Paper2.Certificates.Q6CoverageCompact.Layer07Part003

namespace Paper2.Certificates.Q6.Coverage

def stree7LRRRRLLL (i : Nat) : State := match i with | 0 => state7_849 | 1 => state7_850 | 2 => state7_851 | 3 => state7_852 | 4 => state7_853 | 5 => state7_854 | _ => state7_855

def stree7LRRRRLLR (i : Nat) : State := match i with | 0 => state7_856 | 1 => state7_857 | 2 => state7_858 | 3 => state7_859 | 4 => state7_860 | 5 => state7_861 | _ => state7_862

def stree7LRRRRLL (i : Nat) : State := if i < 7 then stree7LRRRRLLL i else stree7LRRRRLLR (i - 7)

def stree7LRRRRLRL (i : Nat) : State := match i with | 0 => state7_863 | 1 => state7_864 | 2 => state7_865 | 3 => state7_866 | 4 => state7_867 | 5 => state7_868 | _ => state7_869

def stree7LRRRRLRR (i : Nat) : State := match i with | 0 => state7_870 | 1 => state7_871 | 2 => state7_872 | 3 => state7_873 | 4 => state7_874 | 5 => state7_875 | _ => state7_876

def stree7LRRRRLR (i : Nat) : State := if i < 7 then stree7LRRRRLRL i else stree7LRRRRLRR (i - 7)

def stree7LRRRRL (i : Nat) : State := if i < 14 then stree7LRRRRLL i else stree7LRRRRLR (i - 14)

def stree7LRRRRRLL (i : Nat) : State := match i with | 0 => state7_877 | 1 => state7_878 | 2 => state7_879 | 3 => state7_880 | 4 => state7_881 | 5 => state7_882 | _ => state7_883

def stree7LRRRRRLR (i : Nat) : State := match i with | 0 => state7_884 | 1 => state7_885 | 2 => state7_886 | 3 => state7_887 | 4 => state7_888 | 5 => state7_889 | _ => state7_890

def stree7LRRRRRL (i : Nat) : State := if i < 7 then stree7LRRRRRLL i else stree7LRRRRRLR (i - 7)

def stree7LRRRRRRL (i : Nat) : State := match i with | 0 => state7_891 | 1 => state7_892 | 2 => state7_893 | 3 => state7_894 | 4 => state7_895 | 5 => state7_896 | _ => state7_897

def stree7LRRRRRRR (i : Nat) : State := match i with | 0 => state7_898 | 1 => state7_899 | 2 => state7_900 | 3 => state7_901 | 4 => state7_902 | 5 => state7_903 | 6 => state7_904 | _ => state7_905

def stree7LRRRRRR (i : Nat) : State := if i < 7 then stree7LRRRRRRL i else stree7LRRRRRRR (i - 7)

def stree7LRRRRR (i : Nat) : State := if i < 14 then stree7LRRRRRL i else stree7LRRRRRR (i - 14)

def stree7LRRRR (i : Nat) : State := if i < 28 then stree7LRRRRL i else stree7LRRRRR (i - 28)

def stree7LRRR (i : Nat) : State := if i < 57 then stree7LRRRL i else stree7LRRRR (i - 57)

def stree7LRR (i : Nat) : State := if i < 113 then stree7LRRL i else stree7LRRR (i - 113)

def stree7LR (i : Nat) : State := if i < 226 then stree7LRL i else stree7LRR (i - 226)

def stree7L (i : Nat) : State := if i < 453 then stree7LL i else stree7LR (i - 453)

def stree7RLLLLLLL (i : Nat) : State := match i with | 0 => state7_906 | 1 => state7_907 | 2 => state7_908 | 3 => state7_909 | 4 => state7_910 | 5 => state7_911 | _ => state7_912

def stree7RLLLLLLR (i : Nat) : State := match i with | 0 => state7_913 | 1 => state7_914 | 2 => state7_915 | 3 => state7_916 | 4 => state7_917 | 5 => state7_918 | _ => state7_919

def stree7RLLLLLL (i : Nat) : State := if i < 7 then stree7RLLLLLLL i else stree7RLLLLLLR (i - 7)

def stree7RLLLLLRL (i : Nat) : State := match i with | 0 => state7_920 | 1 => state7_921 | 2 => state7_922 | 3 => state7_923 | 4 => state7_924 | 5 => state7_925 | _ => state7_926

def stree7RLLLLLRR (i : Nat) : State := match i with | 0 => state7_927 | 1 => state7_928 | 2 => state7_929 | 3 => state7_930 | 4 => state7_931 | 5 => state7_932 | _ => state7_933

def stree7RLLLLLR (i : Nat) : State := if i < 7 then stree7RLLLLLRL i else stree7RLLLLLRR (i - 7)

def stree7RLLLLL (i : Nat) : State := if i < 14 then stree7RLLLLLL i else stree7RLLLLLR (i - 14)

def stree7RLLLLRLL (i : Nat) : State := match i with | 0 => state7_934 | 1 => state7_935 | 2 => state7_936 | 3 => state7_937 | 4 => state7_938 | 5 => state7_939 | _ => state7_940

def stree7RLLLLRLR (i : Nat) : State := match i with | 0 => state7_941 | 1 => state7_942 | 2 => state7_943 | 3 => state7_944 | 4 => state7_945 | 5 => state7_946 | _ => state7_947

def stree7RLLLLRL (i : Nat) : State := if i < 7 then stree7RLLLLRLL i else stree7RLLLLRLR (i - 7)

def stree7RLLLLRRL (i : Nat) : State := match i with | 0 => state7_948 | 1 => state7_949 | 2 => state7_950 | 3 => state7_951 | 4 => state7_952 | 5 => state7_953 | _ => state7_954

def stree7RLLLLRRR (i : Nat) : State := match i with | 0 => state7_955 | 1 => state7_956 | 2 => state7_957 | 3 => state7_958 | 4 => state7_959 | 5 => state7_960 | _ => state7_961

def stree7RLLLLRR (i : Nat) : State := if i < 7 then stree7RLLLLRRL i else stree7RLLLLRRR (i - 7)

def stree7RLLLLR (i : Nat) : State := if i < 14 then stree7RLLLLRL i else stree7RLLLLRR (i - 14)

def stree7RLLLL (i : Nat) : State := if i < 28 then stree7RLLLLL i else stree7RLLLLR (i - 28)

def stree7RLLLRLLL (i : Nat) : State := match i with | 0 => state7_962 | 1 => state7_963 | 2 => state7_964 | 3 => state7_965 | 4 => state7_966 | 5 => state7_967 | _ => state7_968

def stree7RLLLRLLR (i : Nat) : State := match i with | 0 => state7_969 | 1 => state7_970 | 2 => state7_971 | 3 => state7_972 | 4 => state7_973 | 5 => state7_974 | _ => state7_975

def stree7RLLLRLL (i : Nat) : State := if i < 7 then stree7RLLLRLLL i else stree7RLLLRLLR (i - 7)

def stree7RLLLRLRL (i : Nat) : State := match i with | 0 => state7_976 | 1 => state7_977 | 2 => state7_978 | 3 => state7_979 | 4 => state7_980 | 5 => state7_981 | _ => state7_982

def stree7RLLLRLRR (i : Nat) : State := match i with | 0 => state7_983 | 1 => state7_984 | 2 => state7_985 | 3 => state7_986 | 4 => state7_987 | 5 => state7_988 | _ => state7_989

def stree7RLLLRLR (i : Nat) : State := if i < 7 then stree7RLLLRLRL i else stree7RLLLRLRR (i - 7)

def stree7RLLLRL (i : Nat) : State := if i < 14 then stree7RLLLRLL i else stree7RLLLRLR (i - 14)

def stree7RLLLRRLL (i : Nat) : State := match i with | 0 => state7_990 | 1 => state7_991 | 2 => state7_992 | 3 => state7_993 | 4 => state7_994 | 5 => state7_995 | _ => state7_996

def stree7RLLLRRLR (i : Nat) : State := match i with | 0 => state7_997 | 1 => state7_998 | 2 => state7_999 | 3 => state7_1000 | 4 => state7_1001 | 5 => state7_1002 | _ => state7_1003

def stree7RLLLRRL (i : Nat) : State := if i < 7 then stree7RLLLRRLL i else stree7RLLLRRLR (i - 7)

def stree7RLLLRRRL (i : Nat) : State := match i with | 0 => state7_1004 | 1 => state7_1005 | 2 => state7_1006 | 3 => state7_1007 | 4 => state7_1008 | 5 => state7_1009 | _ => state7_1010

def stree7RLLLRRRR (i : Nat) : State := match i with | 0 => state7_1011 | 1 => state7_1012 | 2 => state7_1013 | 3 => state7_1014 | 4 => state7_1015 | 5 => state7_1016 | 6 => state7_1017 | _ => state7_1018

def stree7RLLLRRR (i : Nat) : State := if i < 7 then stree7RLLLRRRL i else stree7RLLLRRRR (i - 7)

def stree7RLLLRR (i : Nat) : State := if i < 14 then stree7RLLLRRL i else stree7RLLLRRR (i - 14)

def stree7RLLLR (i : Nat) : State := if i < 28 then stree7RLLLRL i else stree7RLLLRR (i - 28)

def stree7RLLL (i : Nat) : State := if i < 56 then stree7RLLLL i else stree7RLLLR (i - 56)

def stree7RLLRLLLL (i : Nat) : State := match i with | 0 => state7_1019 | 1 => state7_1020 | 2 => state7_1021 | 3 => state7_1022 | 4 => state7_1023 | 5 => state7_1024 | _ => state7_1025

def stree7RLLRLLLR (i : Nat) : State := match i with | 0 => state7_1026 | 1 => state7_1027 | 2 => state7_1028 | 3 => state7_1029 | 4 => state7_1030 | 5 => state7_1031 | _ => state7_1032

def stree7RLLRLLL (i : Nat) : State := if i < 7 then stree7RLLRLLLL i else stree7RLLRLLLR (i - 7)

def stree7RLLRLLRL (i : Nat) : State := match i with | 0 => state7_1033 | 1 => state7_1034 | 2 => state7_1035 | 3 => state7_1036 | 4 => state7_1037 | 5 => state7_1038 | _ => state7_1039

def stree7RLLRLLRR (i : Nat) : State := match i with | 0 => state7_1040 | 1 => state7_1041 | 2 => state7_1042 | 3 => state7_1043 | 4 => state7_1044 | 5 => state7_1045 | _ => state7_1046

def stree7RLLRLLR (i : Nat) : State := if i < 7 then stree7RLLRLLRL i else stree7RLLRLLRR (i - 7)

def stree7RLLRLL (i : Nat) : State := if i < 14 then stree7RLLRLLL i else stree7RLLRLLR (i - 14)

def stree7RLLRLRLL (i : Nat) : State := match i with | 0 => state7_1047 | 1 => state7_1048 | 2 => state7_1049 | 3 => state7_1050 | 4 => state7_1051 | 5 => state7_1052 | _ => state7_1053

def stree7RLLRLRLR (i : Nat) : State := match i with | 0 => state7_1054 | 1 => state7_1055 | 2 => state7_1056 | 3 => state7_1057 | 4 => state7_1058 | 5 => state7_1059 | _ => state7_1060

def stree7RLLRLRL (i : Nat) : State := if i < 7 then stree7RLLRLRLL i else stree7RLLRLRLR (i - 7)

def stree7RLLRLRRL (i : Nat) : State := match i with | 0 => state7_1061 | 1 => state7_1062 | 2 => state7_1063 | 3 => state7_1064 | 4 => state7_1065 | 5 => state7_1066 | _ => state7_1067

def stree7RLLRLRRR (i : Nat) : State := match i with | 0 => state7_1068 | 1 => state7_1069 | 2 => state7_1070 | 3 => state7_1071 | 4 => state7_1072 | 5 => state7_1073 | _ => state7_1074

def stree7RLLRLRR (i : Nat) : State := if i < 7 then stree7RLLRLRRL i else stree7RLLRLRRR (i - 7)

def stree7RLLRLR (i : Nat) : State := if i < 14 then stree7RLLRLRL i else stree7RLLRLRR (i - 14)

def stree7RLLRL (i : Nat) : State := if i < 28 then stree7RLLRLL i else stree7RLLRLR (i - 28)

def stree7RLLRRLLL (i : Nat) : State := match i with | 0 => state7_1075 | 1 => state7_1076 | 2 => state7_1077 | 3 => state7_1078 | 4 => state7_1079 | 5 => state7_1080 | _ => state7_1081

def stree7RLLRRLLR (i : Nat) : State := match i with | 0 => state7_1082 | 1 => state7_1083 | 2 => state7_1084 | 3 => state7_1085 | 4 => state7_1086 | 5 => state7_1087 | _ => state7_1088

def stree7RLLRRLL (i : Nat) : State := if i < 7 then stree7RLLRRLLL i else stree7RLLRRLLR (i - 7)

def stree7RLLRRLRL (i : Nat) : State := match i with | 0 => state7_1089 | 1 => state7_1090 | 2 => state7_1091 | 3 => state7_1092 | 4 => state7_1093 | 5 => state7_1094 | _ => state7_1095

def stree7RLLRRLRR (i : Nat) : State := match i with | 0 => state7_1096 | 1 => state7_1097 | 2 => state7_1098 | 3 => state7_1099 | 4 => state7_1100 | 5 => state7_1101 | _ => state7_1102

def stree7RLLRRLR (i : Nat) : State := if i < 7 then stree7RLLRRLRL i else stree7RLLRRLRR (i - 7)

def stree7RLLRRL (i : Nat) : State := if i < 14 then stree7RLLRRLL i else stree7RLLRRLR (i - 14)

def stree7RLLRRRLL (i : Nat) : State := match i with | 0 => state7_1103 | 1 => state7_1104 | 2 => state7_1105 | 3 => state7_1106 | 4 => state7_1107 | 5 => state7_1108 | _ => state7_1109

def stree7RLLRRRLR (i : Nat) : State := match i with | 0 => state7_1110 | 1 => state7_1111 | 2 => state7_1112 | 3 => state7_1113 | 4 => state7_1114 | 5 => state7_1115 | _ => state7_1116

def stree7RLLRRRL (i : Nat) : State := if i < 7 then stree7RLLRRRLL i else stree7RLLRRRLR (i - 7)

def stree7RLLRRRRL (i : Nat) : State := match i with | 0 => state7_1117 | 1 => state7_1118 | 2 => state7_1119 | 3 => state7_1120 | 4 => state7_1121 | 5 => state7_1122 | _ => state7_1123

def stree7RLLRRRRR (i : Nat) : State := match i with | 0 => state7_1124 | 1 => state7_1125 | 2 => state7_1126 | 3 => state7_1127 | 4 => state7_1128 | 5 => state7_1129 | 6 => state7_1130 | _ => state7_1131

def stree7RLLRRRR (i : Nat) : State := if i < 7 then stree7RLLRRRRL i else stree7RLLRRRRR (i - 7)

def stree7RLLRRR (i : Nat) : State := if i < 14 then stree7RLLRRRL i else stree7RLLRRRR (i - 14)

def stree7RLLRR (i : Nat) : State := if i < 28 then stree7RLLRRL i else stree7RLLRRR (i - 28)

def stree7RLLR (i : Nat) : State := if i < 56 then stree7RLLRL i else stree7RLLRR (i - 56)

def stree7RLL (i : Nat) : State := if i < 113 then stree7RLLL i else stree7RLLR (i - 113)

def stree7RLRLLLLL (i : Nat) : State := match i with | 0 => state7_1132 | 1 => state7_1133 | 2 => state7_1134 | 3 => state7_1135 | 4 => state7_1136 | 5 => state7_1137 | _ => state7_1138

def stree7RLRLLLLR (i : Nat) : State := match i with | 0 => state7_1139 | 1 => state7_1140 | 2 => state7_1141 | 3 => state7_1142 | 4 => state7_1143 | 5 => state7_1144 | _ => state7_1145

def stree7RLRLLLL (i : Nat) : State := if i < 7 then stree7RLRLLLLL i else stree7RLRLLLLR (i - 7)

def stree7RLRLLLRL (i : Nat) : State := match i with | 0 => state7_1146 | 1 => state7_1147 | 2 => state7_1148 | 3 => state7_1149 | 4 => state7_1150 | 5 => state7_1151 | _ => state7_1152

def stree7RLRLLLRR (i : Nat) : State := match i with | 0 => state7_1153 | 1 => state7_1154 | 2 => state7_1155 | 3 => state7_1156 | 4 => state7_1157 | 5 => state7_1158 | _ => state7_1159

def stree7RLRLLLR (i : Nat) : State := if i < 7 then stree7RLRLLLRL i else stree7RLRLLLRR (i - 7)

def stree7RLRLLL (i : Nat) : State := if i < 14 then stree7RLRLLLL i else stree7RLRLLLR (i - 14)

def stree7RLRLLRLL (i : Nat) : State := match i with | 0 => state7_1160 | 1 => state7_1161 | 2 => state7_1162 | 3 => state7_1163 | 4 => state7_1164 | 5 => state7_1165 | _ => state7_1166

def stree7RLRLLRLR (i : Nat) : State := match i with | 0 => state7_1167 | 1 => state7_1168 | 2 => state7_1169 | 3 => state7_1170 | 4 => state7_1171 | 5 => state7_1172 | _ => state7_1173

def stree7RLRLLRL (i : Nat) : State := if i < 7 then stree7RLRLLRLL i else stree7RLRLLRLR (i - 7)

def stree7RLRLLRRL (i : Nat) : State := match i with | 0 => state7_1174 | 1 => state7_1175 | 2 => state7_1176 | 3 => state7_1177 | 4 => state7_1178 | 5 => state7_1179 | _ => state7_1180

def stree7RLRLLRRR (i : Nat) : State := match i with | 0 => state7_1181 | 1 => state7_1182 | 2 => state7_1183 | 3 => state7_1184 | 4 => state7_1185 | 5 => state7_1186 | _ => state7_1187

def stree7RLRLLRR (i : Nat) : State := if i < 7 then stree7RLRLLRRL i else stree7RLRLLRRR (i - 7)

def stree7RLRLLR (i : Nat) : State := if i < 14 then stree7RLRLLRL i else stree7RLRLLRR (i - 14)

def stree7RLRLL (i : Nat) : State := if i < 28 then stree7RLRLLL i else stree7RLRLLR (i - 28)

def stree7RLRLRLLL (i : Nat) : State := match i with | 0 => state7_1188 | 1 => state7_1189 | 2 => state7_1190 | 3 => state7_1191 | 4 => state7_1192 | 5 => state7_1193 | _ => state7_1194

def stree7RLRLRLLR (i : Nat) : State := match i with | 0 => state7_1195 | 1 => state7_1196 | 2 => state7_1197 | 3 => state7_1198 | 4 => state7_1199 | 5 => state7_1200 | _ => state7_1201

def stree7RLRLRLL (i : Nat) : State := if i < 7 then stree7RLRLRLLL i else stree7RLRLRLLR (i - 7)

def stree7RLRLRLRL (i : Nat) : State := match i with | 0 => state7_1202 | 1 => state7_1203 | 2 => state7_1204 | 3 => state7_1205 | 4 => state7_1206 | 5 => state7_1207 | _ => state7_1208

def stree7RLRLRLRR (i : Nat) : State := match i with | 0 => state7_1209 | 1 => state7_1210 | 2 => state7_1211 | 3 => state7_1212 | 4 => state7_1213 | 5 => state7_1214 | _ => state7_1215

def stree7RLRLRLR (i : Nat) : State := if i < 7 then stree7RLRLRLRL i else stree7RLRLRLRR (i - 7)

def stree7RLRLRL (i : Nat) : State := if i < 14 then stree7RLRLRLL i else stree7RLRLRLR (i - 14)

def stree7RLRLRRLL (i : Nat) : State := match i with | 0 => state7_1216 | 1 => state7_1217 | 2 => state7_1218 | 3 => state7_1219 | 4 => state7_1220 | 5 => state7_1221 | _ => state7_1222

def stree7RLRLRRLR (i : Nat) : State := match i with | 0 => state7_1223 | 1 => state7_1224 | 2 => state7_1225 | 3 => state7_1226 | 4 => state7_1227 | 5 => state7_1228 | _ => state7_1229

def stree7RLRLRRL (i : Nat) : State := if i < 7 then stree7RLRLRRLL i else stree7RLRLRRLR (i - 7)

def stree7RLRLRRRL (i : Nat) : State := match i with | 0 => state7_1230 | 1 => state7_1231 | 2 => state7_1232 | 3 => state7_1233 | 4 => state7_1234 | 5 => state7_1235 | _ => state7_1236

def stree7RLRLRRRR (i : Nat) : State := match i with | 0 => state7_1237 | 1 => state7_1238 | 2 => state7_1239 | 3 => state7_1240 | 4 => state7_1241 | 5 => state7_1242 | 6 => state7_1243 | _ => state7_1244

def stree7RLRLRRR (i : Nat) : State := if i < 7 then stree7RLRLRRRL i else stree7RLRLRRRR (i - 7)

def stree7RLRLRR (i : Nat) : State := if i < 14 then stree7RLRLRRL i else stree7RLRLRRR (i - 14)

def stree7RLRLR (i : Nat) : State := if i < 28 then stree7RLRLRL i else stree7RLRLRR (i - 28)

def stree7RLRL (i : Nat) : State := if i < 56 then stree7RLRLL i else stree7RLRLR (i - 56)

def stree7RLRRLLLL (i : Nat) : State := match i with | 0 => state7_1245 | 1 => state7_1246 | 2 => state7_1247 | 3 => state7_1248 | 4 => state7_1249 | 5 => state7_1250 | _ => state7_1251

def stree7RLRRLLLR (i : Nat) : State := match i with | 0 => state7_1252 | 1 => state7_1253 | 2 => state7_1254 | 3 => state7_1255 | 4 => state7_1256 | 5 => state7_1257 | _ => state7_1258

def stree7RLRRLLL (i : Nat) : State := if i < 7 then stree7RLRRLLLL i else stree7RLRRLLLR (i - 7)

def stree7RLRRLLRL (i : Nat) : State := match i with | 0 => state7_1259 | 1 => state7_1260 | 2 => state7_1261 | 3 => state7_1262 | 4 => state7_1263 | 5 => state7_1264 | _ => state7_1265

def stree7RLRRLLRR (i : Nat) : State := match i with | 0 => state7_1266 | 1 => state7_1267 | 2 => state7_1268 | 3 => state7_1269 | 4 => state7_1270 | 5 => state7_1271 | _ => state7_1272

def stree7RLRRLLR (i : Nat) : State := if i < 7 then stree7RLRRLLRL i else stree7RLRRLLRR (i - 7)

def stree7RLRRLL (i : Nat) : State := if i < 14 then stree7RLRRLLL i else stree7RLRRLLR (i - 14)

def stree7RLRRLRLL (i : Nat) : State := match i with | 0 => state7_1273 | 1 => state7_1274 | 2 => state7_1275 | 3 => state7_1276 | 4 => state7_1277 | 5 => state7_1278 | _ => state7_1279

def stree7RLRRLRLR (i : Nat) : State := match i with | 0 => state7_1280 | 1 => state7_1281 | 2 => state7_1282 | 3 => state7_1283 | 4 => state7_1284 | 5 => state7_1285 | _ => state7_1286

def stree7RLRRLRL (i : Nat) : State := if i < 7 then stree7RLRRLRLL i else stree7RLRRLRLR (i - 7)

def stree7RLRRLRRL (i : Nat) : State := match i with | 0 => state7_1287 | 1 => state7_1288 | 2 => state7_1289 | 3 => state7_1290 | 4 => state7_1291 | 5 => state7_1292 | _ => state7_1293

def stree7RLRRLRRR (i : Nat) : State := match i with | 0 => state7_1294 | 1 => state7_1295 | 2 => state7_1296 | 3 => state7_1297 | 4 => state7_1298 | 5 => state7_1299 | 6 => state7_1300 | _ => state7_1301

def stree7RLRRLRR (i : Nat) : State := if i < 7 then stree7RLRRLRRL i else stree7RLRRLRRR (i - 7)

def stree7RLRRLR (i : Nat) : State := if i < 14 then stree7RLRRLRL i else stree7RLRRLRR (i - 14)

def stree7RLRRL (i : Nat) : State := if i < 28 then stree7RLRRLL i else stree7RLRRLR (i - 28)

def stree7RLRRRLLL (i : Nat) : State := match i with | 0 => state7_1302 | 1 => state7_1303 | 2 => state7_1304 | 3 => state7_1305 | 4 => state7_1306 | 5 => state7_1307 | _ => state7_1308

def stree7RLRRRLLR (i : Nat) : State := match i with | 0 => state7_1309 | 1 => state7_1310 | 2 => state7_1311 | 3 => state7_1312 | 4 => state7_1313 | 5 => state7_1314 | _ => state7_1315

def stree7RLRRRLL (i : Nat) : State := if i < 7 then stree7RLRRRLLL i else stree7RLRRRLLR (i - 7)

def stree7RLRRRLRL (i : Nat) : State := match i with | 0 => state7_1316 | 1 => state7_1317 | 2 => state7_1318 | 3 => state7_1319 | 4 => state7_1320 | 5 => state7_1321 | _ => state7_1322

def stree7RLRRRLRR (i : Nat) : State := match i with | 0 => state7_1323 | 1 => state7_1324 | 2 => state7_1325 | 3 => state7_1326 | 4 => state7_1327 | 5 => state7_1328 | _ => state7_1329

def stree7RLRRRLR (i : Nat) : State := if i < 7 then stree7RLRRRLRL i else stree7RLRRRLRR (i - 7)

def stree7RLRRRL (i : Nat) : State := if i < 14 then stree7RLRRRLL i else stree7RLRRRLR (i - 14)

def stree7RLRRRRLL (i : Nat) : State := match i with | 0 => state7_1330 | 1 => state7_1331 | 2 => state7_1332 | 3 => state7_1333 | 4 => state7_1334 | 5 => state7_1335 | _ => state7_1336

def stree7RLRRRRLR (i : Nat) : State := match i with | 0 => state7_1337 | 1 => state7_1338 | 2 => state7_1339 | 3 => state7_1340 | 4 => state7_1341 | 5 => state7_1342 | _ => state7_1343

def stree7RLRRRRL (i : Nat) : State := if i < 7 then stree7RLRRRRLL i else stree7RLRRRRLR (i - 7)

def stree7RLRRRRRL (i : Nat) : State := match i with | 0 => state7_1344 | 1 => state7_1345 | 2 => state7_1346 | 3 => state7_1347 | 4 => state7_1348 | 5 => state7_1349 | _ => state7_1350

def stree7RLRRRRRR (i : Nat) : State := match i with | 0 => state7_1351 | 1 => state7_1352 | 2 => state7_1353 | 3 => state7_1354 | 4 => state7_1355 | 5 => state7_1356 | 6 => state7_1357 | _ => state7_1358

def stree7RLRRRRR (i : Nat) : State := if i < 7 then stree7RLRRRRRL i else stree7RLRRRRRR (i - 7)

def stree7RLRRRR (i : Nat) : State := if i < 14 then stree7RLRRRRL i else stree7RLRRRRR (i - 14)

def stree7RLRRR (i : Nat) : State := if i < 28 then stree7RLRRRL i else stree7RLRRRR (i - 28)

def stree7RLRR (i : Nat) : State := if i < 57 then stree7RLRRL i else stree7RLRRR (i - 57)

def stree7RLR (i : Nat) : State := if i < 113 then stree7RLRL i else stree7RLRR (i - 113)

def stree7RL (i : Nat) : State := if i < 226 then stree7RLL i else stree7RLR (i - 226)

def stree7RRLLLLLL (i : Nat) : State := match i with | 0 => state7_1359 | 1 => state7_1360 | 2 => state7_1361 | 3 => state7_1362 | 4 => state7_1363 | 5 => state7_1364 | _ => state7_1365

def stree7RRLLLLLR (i : Nat) : State := match i with | 0 => state7_1366 | 1 => state7_1367 | 2 => state7_1368 | 3 => state7_1369 | 4 => state7_1370 | 5 => state7_1371 | _ => state7_1372

def stree7RRLLLLL (i : Nat) : State := if i < 7 then stree7RRLLLLLL i else stree7RRLLLLLR (i - 7)

def stree7RRLLLLRL (i : Nat) : State := match i with | 0 => state7_1373 | 1 => state7_1374 | 2 => state7_1375 | 3 => state7_1376 | 4 => state7_1377 | 5 => state7_1378 | _ => state7_1379

def stree7RRLLLLRR (i : Nat) : State := match i with | 0 => state7_1380 | 1 => state7_1381 | 2 => state7_1382 | 3 => state7_1383 | 4 => state7_1384 | 5 => state7_1385 | _ => state7_1386

def stree7RRLLLLR (i : Nat) : State := if i < 7 then stree7RRLLLLRL i else stree7RRLLLLRR (i - 7)

def stree7RRLLLL (i : Nat) : State := if i < 14 then stree7RRLLLLL i else stree7RRLLLLR (i - 14)

def stree7RRLLLRLL (i : Nat) : State := match i with | 0 => state7_1387 | 1 => state7_1388 | 2 => state7_1389 | 3 => state7_1390 | 4 => state7_1391 | 5 => state7_1392 | _ => state7_1393

def stree7RRLLLRLR (i : Nat) : State := match i with | 0 => state7_1394 | 1 => state7_1395 | 2 => state7_1396 | 3 => state7_1397 | 4 => state7_1398 | 5 => state7_1399 | _ => state7_1400

def stree7RRLLLRL (i : Nat) : State := if i < 7 then stree7RRLLLRLL i else stree7RRLLLRLR (i - 7)

def stree7RRLLLRRL (i : Nat) : State := match i with | 0 => state7_1401 | 1 => state7_1402 | 2 => state7_1403 | 3 => state7_1404 | 4 => state7_1405 | 5 => state7_1406 | _ => state7_1407

def stree7RRLLLRRR (i : Nat) : State := match i with | 0 => state7_1408 | 1 => state7_1409 | 2 => state7_1410 | 3 => state7_1411 | 4 => state7_1412 | 5 => state7_1413 | _ => state7_1414

def stree7RRLLLRR (i : Nat) : State := if i < 7 then stree7RRLLLRRL i else stree7RRLLLRRR (i - 7)

def stree7RRLLLR (i : Nat) : State := if i < 14 then stree7RRLLLRL i else stree7RRLLLRR (i - 14)

def stree7RRLLL (i : Nat) : State := if i < 28 then stree7RRLLLL i else stree7RRLLLR (i - 28)

def stree7RRLLRLLL (i : Nat) : State := match i with | 0 => state7_1415 | 1 => state7_1416 | 2 => state7_1417 | 3 => state7_1418 | 4 => state7_1419 | 5 => state7_1420 | _ => state7_1421

def stree7RRLLRLLR (i : Nat) : State := match i with | 0 => state7_1422 | 1 => state7_1423 | 2 => state7_1424 | 3 => state7_1425 | 4 => state7_1426 | 5 => state7_1427 | _ => state7_1428

def stree7RRLLRLL (i : Nat) : State := if i < 7 then stree7RRLLRLLL i else stree7RRLLRLLR (i - 7)

def stree7RRLLRLRL (i : Nat) : State := match i with | 0 => state7_1429 | 1 => state7_1430 | 2 => state7_1431 | 3 => state7_1432 | 4 => state7_1433 | 5 => state7_1434 | _ => state7_1435

def stree7RRLLRLRR (i : Nat) : State := match i with | 0 => state7_1436 | 1 => state7_1437 | 2 => state7_1438 | 3 => state7_1439 | 4 => state7_1440 | 5 => state7_1441 | _ => state7_1442

def stree7RRLLRLR (i : Nat) : State := if i < 7 then stree7RRLLRLRL i else stree7RRLLRLRR (i - 7)

def stree7RRLLRL (i : Nat) : State := if i < 14 then stree7RRLLRLL i else stree7RRLLRLR (i - 14)

def stree7RRLLRRLL (i : Nat) : State := match i with | 0 => state7_1443 | 1 => state7_1444 | 2 => state7_1445 | 3 => state7_1446 | 4 => state7_1447 | 5 => state7_1448 | _ => state7_1449

def stree7RRLLRRLR (i : Nat) : State := match i with | 0 => state7_1450 | 1 => state7_1451 | 2 => state7_1452 | 3 => state7_1453 | 4 => state7_1454 | 5 => state7_1455 | _ => state7_1456

def stree7RRLLRRL (i : Nat) : State := if i < 7 then stree7RRLLRRLL i else stree7RRLLRRLR (i - 7)

def stree7RRLLRRRL (i : Nat) : State := match i with | 0 => state7_1457 | 1 => state7_1458 | 2 => state7_1459 | 3 => state7_1460 | 4 => state7_1461 | 5 => state7_1462 | _ => state7_1463

def stree7RRLLRRRR (i : Nat) : State := match i with | 0 => state7_1464 | 1 => state7_1465 | 2 => state7_1466 | 3 => state7_1467 | 4 => state7_1468 | 5 => state7_1469 | 6 => state7_1470 | _ => state7_1471

def stree7RRLLRRR (i : Nat) : State := if i < 7 then stree7RRLLRRRL i else stree7RRLLRRRR (i - 7)

def stree7RRLLRR (i : Nat) : State := if i < 14 then stree7RRLLRRL i else stree7RRLLRRR (i - 14)

def stree7RRLLR (i : Nat) : State := if i < 28 then stree7RRLLRL i else stree7RRLLRR (i - 28)

def stree7RRLL (i : Nat) : State := if i < 56 then stree7RRLLL i else stree7RRLLR (i - 56)

def stree7RRLRLLLL (i : Nat) : State := match i with | 0 => state7_1472 | 1 => state7_1473 | 2 => state7_1474 | 3 => state7_1475 | 4 => state7_1476 | 5 => state7_1477 | _ => state7_1478

def stree7RRLRLLLR (i : Nat) : State := match i with | 0 => state7_1479 | 1 => state7_1480 | 2 => state7_1481 | 3 => state7_1482 | 4 => state7_1483 | 5 => state7_1484 | _ => state7_1485

def stree7RRLRLLL (i : Nat) : State := if i < 7 then stree7RRLRLLLL i else stree7RRLRLLLR (i - 7)

def stree7RRLRLLRL (i : Nat) : State := match i with | 0 => state7_1486 | 1 => state7_1487 | 2 => state7_1488 | 3 => state7_1489 | 4 => state7_1490 | 5 => state7_1491 | _ => state7_1492

def stree7RRLRLLRR (i : Nat) : State := match i with | 0 => state7_1493 | 1 => state7_1494 | 2 => state7_1495 | 3 => state7_1496 | 4 => state7_1497 | 5 => state7_1498 | _ => state7_1499

def stree7RRLRLLR (i : Nat) : State := if i < 7 then stree7RRLRLLRL i else stree7RRLRLLRR (i - 7)

def stree7RRLRLL (i : Nat) : State := if i < 14 then stree7RRLRLLL i else stree7RRLRLLR (i - 14)

def stree7RRLRLRLL (i : Nat) : State := match i with | 0 => state7_1500 | 1 => state7_1501 | 2 => state7_1502 | 3 => state7_1503 | 4 => state7_1504 | 5 => state7_1505 | _ => state7_1506

def stree7RRLRLRLR (i : Nat) : State := match i with | 0 => state7_1507 | 1 => state7_1508 | 2 => state7_1509 | 3 => state7_1510 | 4 => state7_1511 | 5 => state7_1512 | _ => state7_1513

def stree7RRLRLRL (i : Nat) : State := if i < 7 then stree7RRLRLRLL i else stree7RRLRLRLR (i - 7)

def stree7RRLRLRRL (i : Nat) : State := match i with | 0 => state7_1514 | 1 => state7_1515 | 2 => state7_1516 | 3 => state7_1517 | 4 => state7_1518 | 5 => state7_1519 | _ => state7_1520

def stree7RRLRLRRR (i : Nat) : State := match i with | 0 => state7_1521 | 1 => state7_1522 | 2 => state7_1523 | 3 => state7_1524 | 4 => state7_1525 | 5 => state7_1526 | _ => state7_1527

def stree7RRLRLRR (i : Nat) : State := if i < 7 then stree7RRLRLRRL i else stree7RRLRLRRR (i - 7)

def stree7RRLRLR (i : Nat) : State := if i < 14 then stree7RRLRLRL i else stree7RRLRLRR (i - 14)

def stree7RRLRL (i : Nat) : State := if i < 28 then stree7RRLRLL i else stree7RRLRLR (i - 28)

def stree7RRLRRLLL (i : Nat) : State := match i with | 0 => state7_1528 | 1 => state7_1529 | 2 => state7_1530 | 3 => state7_1531 | 4 => state7_1532 | 5 => state7_1533 | _ => state7_1534

def stree7RRLRRLLR (i : Nat) : State := match i with | 0 => state7_1535 | 1 => state7_1536 | 2 => state7_1537 | 3 => state7_1538 | 4 => state7_1539 | 5 => state7_1540 | _ => state7_1541

def stree7RRLRRLL (i : Nat) : State := if i < 7 then stree7RRLRRLLL i else stree7RRLRRLLR (i - 7)

def stree7RRLRRLRL (i : Nat) : State := match i with | 0 => state7_1542 | 1 => state7_1543 | 2 => state7_1544 | 3 => state7_1545 | 4 => state7_1546 | 5 => state7_1547 | _ => state7_1548

def stree7RRLRRLRR (i : Nat) : State := match i with | 0 => state7_1549 | 1 => state7_1550 | 2 => state7_1551 | 3 => state7_1552 | 4 => state7_1553 | 5 => state7_1554 | _ => state7_1555

def stree7RRLRRLR (i : Nat) : State := if i < 7 then stree7RRLRRLRL i else stree7RRLRRLRR (i - 7)

def stree7RRLRRL (i : Nat) : State := if i < 14 then stree7RRLRRLL i else stree7RRLRRLR (i - 14)

def stree7RRLRRRLL (i : Nat) : State := match i with | 0 => state7_1556 | 1 => state7_1557 | 2 => state7_1558 | 3 => state7_1559 | 4 => state7_1560 | 5 => state7_1561 | _ => state7_1562

def stree7RRLRRRLR (i : Nat) : State := match i with | 0 => state7_1563 | 1 => state7_1564 | 2 => state7_1565 | 3 => state7_1566 | 4 => state7_1567 | 5 => state7_1568 | _ => state7_1569

def stree7RRLRRRL (i : Nat) : State := if i < 7 then stree7RRLRRRLL i else stree7RRLRRRLR (i - 7)

def stree7RRLRRRRL (i : Nat) : State := match i with | 0 => state7_1570 | 1 => state7_1571 | 2 => state7_1572 | 3 => state7_1573 | 4 => state7_1574 | 5 => state7_1575 | _ => state7_1576

def stree7RRLRRRRR (i : Nat) : State := match i with | 0 => state7_1577 | 1 => state7_1578 | 2 => state7_1579 | 3 => state7_1580 | 4 => state7_1581 | 5 => state7_1582 | 6 => state7_1583 | _ => state7_1584

def stree7RRLRRRR (i : Nat) : State := if i < 7 then stree7RRLRRRRL i else stree7RRLRRRRR (i - 7)

def stree7RRLRRR (i : Nat) : State := if i < 14 then stree7RRLRRRL i else stree7RRLRRRR (i - 14)

def stree7RRLRR (i : Nat) : State := if i < 28 then stree7RRLRRL i else stree7RRLRRR (i - 28)

def stree7RRLR (i : Nat) : State := if i < 56 then stree7RRLRL i else stree7RRLRR (i - 56)

def stree7RRL (i : Nat) : State := if i < 113 then stree7RRLL i else stree7RRLR (i - 113)

def stree7RRRLLLLL (i : Nat) : State := match i with | 0 => state7_1585 | 1 => state7_1586 | 2 => state7_1587 | 3 => state7_1588 | 4 => state7_1589 | 5 => state7_1590 | _ => state7_1591

def stree7RRRLLLLR (i : Nat) : State := match i with | 0 => state7_1592 | 1 => state7_1593 | 2 => state7_1594 | 3 => state7_1595 | 4 => state7_1596 | 5 => state7_1597 | _ => state7_1598

def stree7RRRLLLL (i : Nat) : State := if i < 7 then stree7RRRLLLLL i else stree7RRRLLLLR (i - 7)

def stree7RRRLLLRL (i : Nat) : State := match i with | 0 => state7_1599 | 1 => state7_1600 | 2 => state7_1601 | 3 => state7_1602 | 4 => state7_1603 | 5 => state7_1604 | _ => state7_1605

def stree7RRRLLLRR (i : Nat) : State := match i with | 0 => state7_1606 | 1 => state7_1607 | 2 => state7_1608 | 3 => state7_1609 | 4 => state7_1610 | 5 => state7_1611 | _ => state7_1612

def stree7RRRLLLR (i : Nat) : State := if i < 7 then stree7RRRLLLRL i else stree7RRRLLLRR (i - 7)

def stree7RRRLLL (i : Nat) : State := if i < 14 then stree7RRRLLLL i else stree7RRRLLLR (i - 14)

def stree7RRRLLRLL (i : Nat) : State := match i with | 0 => state7_1613 | 1 => state7_1614 | 2 => state7_1615 | 3 => state7_1616 | 4 => state7_1617 | 5 => state7_1618 | _ => state7_1619

def stree7RRRLLRLR (i : Nat) : State := match i with | 0 => state7_1620 | 1 => state7_1621 | 2 => state7_1622 | 3 => state7_1623 | 4 => state7_1624 | 5 => state7_1625 | _ => state7_1626

def stree7RRRLLRL (i : Nat) : State := if i < 7 then stree7RRRLLRLL i else stree7RRRLLRLR (i - 7)

def stree7RRRLLRRL (i : Nat) : State := match i with | 0 => state7_1627 | 1 => state7_1628 | 2 => state7_1629 | 3 => state7_1630 | 4 => state7_1631 | 5 => state7_1632 | _ => state7_1633

def stree7RRRLLRRR (i : Nat) : State := match i with | 0 => state7_1634 | 1 => state7_1635 | 2 => state7_1636 | 3 => state7_1637 | 4 => state7_1638 | 5 => state7_1639 | _ => state7_1640

def stree7RRRLLRR (i : Nat) : State := if i < 7 then stree7RRRLLRRL i else stree7RRRLLRRR (i - 7)

def stree7RRRLLR (i : Nat) : State := if i < 14 then stree7RRRLLRL i else stree7RRRLLRR (i - 14)

def stree7RRRLL (i : Nat) : State := if i < 28 then stree7RRRLLL i else stree7RRRLLR (i - 28)

def stree7RRRLRLLL (i : Nat) : State := match i with | 0 => state7_1641 | 1 => state7_1642 | 2 => state7_1643 | 3 => state7_1644 | 4 => state7_1645 | 5 => state7_1646 | _ => state7_1647

def stree7RRRLRLLR (i : Nat) : State := match i with | 0 => state7_1648 | 1 => state7_1649 | 2 => state7_1650 | 3 => state7_1651 | 4 => state7_1652 | 5 => state7_1653 | _ => state7_1654

def stree7RRRLRLL (i : Nat) : State := if i < 7 then stree7RRRLRLLL i else stree7RRRLRLLR (i - 7)

def stree7RRRLRLRL (i : Nat) : State := match i with | 0 => state7_1655 | 1 => state7_1656 | 2 => state7_1657 | 3 => state7_1658 | 4 => state7_1659 | 5 => state7_1660 | _ => state7_1661

def stree7RRRLRLRR (i : Nat) : State := match i with | 0 => state7_1662 | 1 => state7_1663 | 2 => state7_1664 | 3 => state7_1665 | 4 => state7_1666 | 5 => state7_1667 | _ => state7_1668

def stree7RRRLRLR (i : Nat) : State := if i < 7 then stree7RRRLRLRL i else stree7RRRLRLRR (i - 7)

def stree7RRRLRL (i : Nat) : State := if i < 14 then stree7RRRLRLL i else stree7RRRLRLR (i - 14)

def stree7RRRLRRLL (i : Nat) : State := match i with | 0 => state7_1669 | 1 => state7_1670 | 2 => state7_1671 | 3 => state7_1672 | 4 => state7_1673 | 5 => state7_1674 | _ => state7_1675

def stree7RRRLRRLR (i : Nat) : State := match i with | 0 => state7_1676 | 1 => state7_1677 | 2 => state7_1678 | 3 => state7_1679 | 4 => state7_1680 | 5 => state7_1681 | _ => state7_1682

def stree7RRRLRRL (i : Nat) : State := if i < 7 then stree7RRRLRRLL i else stree7RRRLRRLR (i - 7)

def stree7RRRLRRRL (i : Nat) : State := match i with | 0 => state7_1683 | 1 => state7_1684 | 2 => state7_1685 | 3 => state7_1686 | 4 => state7_1687 | 5 => state7_1688 | _ => state7_1689

def stree7RRRLRRRR (i : Nat) : State := match i with | 0 => state7_1690 | 1 => state7_1691 | 2 => state7_1692 | 3 => state7_1693 | 4 => state7_1694 | 5 => state7_1695 | 6 => state7_1696 | _ => state7_1697

def stree7RRRLRRR (i : Nat) : State := if i < 7 then stree7RRRLRRRL i else stree7RRRLRRRR (i - 7)

def stree7RRRLRR (i : Nat) : State := if i < 14 then stree7RRRLRRL i else stree7RRRLRRR (i - 14)

def stree7RRRLR (i : Nat) : State := if i < 28 then stree7RRRLRL i else stree7RRRLRR (i - 28)

def stree7RRRL (i : Nat) : State := if i < 56 then stree7RRRLL i else stree7RRRLR (i - 56)

def stree7RRRRLLLL (i : Nat) : State := match i with | 0 => state7_1698 | 1 => state7_1699 | 2 => state7_1700 | 3 => state7_1701 | 4 => state7_1702 | 5 => state7_1703 | _ => state7_1704

def stree7RRRRLLLR (i : Nat) : State := match i with | 0 => state7_1705 | 1 => state7_1706 | 2 => state7_1707 | 3 => state7_1708 | 4 => state7_1709 | 5 => state7_1710 | _ => state7_1711

def stree7RRRRLLL (i : Nat) : State := if i < 7 then stree7RRRRLLLL i else stree7RRRRLLLR (i - 7)

def stree7RRRRLLRL (i : Nat) : State := match i with | 0 => state7_1712 | 1 => state7_1713 | 2 => state7_1714 | 3 => state7_1715 | 4 => state7_1716 | 5 => state7_1717 | _ => state7_1718

def stree7RRRRLLRR (i : Nat) : State := match i with | 0 => state7_1719 | 1 => state7_1720 | 2 => state7_1721 | 3 => state7_1722 | 4 => state7_1723 | 5 => state7_1724 | _ => state7_1725

def stree7RRRRLLR (i : Nat) : State := if i < 7 then stree7RRRRLLRL i else stree7RRRRLLRR (i - 7)

def stree7RRRRLL (i : Nat) : State := if i < 14 then stree7RRRRLLL i else stree7RRRRLLR (i - 14)

def stree7RRRRLRLL (i : Nat) : State := match i with | 0 => state7_1726 | 1 => state7_1727 | 2 => state7_1728 | 3 => state7_1729 | 4 => state7_1730 | 5 => state7_1731 | _ => state7_1732

def stree7RRRRLRLR (i : Nat) : State := match i with | 0 => state7_1733 | 1 => state7_1734 | 2 => state7_1735 | 3 => state7_1736 | 4 => state7_1737 | 5 => state7_1738 | _ => state7_1739

def stree7RRRRLRL (i : Nat) : State := if i < 7 then stree7RRRRLRLL i else stree7RRRRLRLR (i - 7)

def stree7RRRRLRRL (i : Nat) : State := match i with | 0 => state7_1740 | 1 => state7_1741 | 2 => state7_1742 | 3 => state7_1743 | 4 => state7_1744 | 5 => state7_1745 | _ => state7_1746

def stree7RRRRLRRR (i : Nat) : State := match i with | 0 => state7_1747 | 1 => state7_1748 | 2 => state7_1749 | 3 => state7_1750 | 4 => state7_1751 | 5 => state7_1752 | 6 => state7_1753 | _ => state7_1754

def stree7RRRRLRR (i : Nat) : State := if i < 7 then stree7RRRRLRRL i else stree7RRRRLRRR (i - 7)

def stree7RRRRLR (i : Nat) : State := if i < 14 then stree7RRRRLRL i else stree7RRRRLRR (i - 14)

def stree7RRRRL (i : Nat) : State := if i < 28 then stree7RRRRLL i else stree7RRRRLR (i - 28)

def stree7RRRRRLLL (i : Nat) : State := match i with | 0 => state7_1755 | 1 => state7_1756 | 2 => state7_1757 | 3 => state7_1758 | 4 => state7_1759 | 5 => state7_1760 | _ => state7_1761

def stree7RRRRRLLR (i : Nat) : State := match i with | 0 => state7_1762 | 1 => state7_1763 | 2 => state7_1764 | 3 => state7_1765 | 4 => state7_1766 | 5 => state7_1767 | _ => state7_1768

def stree7RRRRRLL (i : Nat) : State := if i < 7 then stree7RRRRRLLL i else stree7RRRRRLLR (i - 7)

def stree7RRRRRLRL (i : Nat) : State := match i with | 0 => state7_1769 | 1 => state7_1770 | 2 => state7_1771 | 3 => state7_1772 | 4 => state7_1773 | 5 => state7_1774 | _ => state7_1775

def stree7RRRRRLRR (i : Nat) : State := match i with | 0 => state7_1776 | 1 => state7_1777 | 2 => state7_1778 | 3 => state7_1779 | 4 => state7_1780 | 5 => state7_1781 | _ => state7_1782

def stree7RRRRRLR (i : Nat) : State := if i < 7 then stree7RRRRRLRL i else stree7RRRRRLRR (i - 7)

def stree7RRRRRL (i : Nat) : State := if i < 14 then stree7RRRRRLL i else stree7RRRRRLR (i - 14)

def stree7RRRRRRLL (i : Nat) : State := match i with | 0 => state7_1783 | 1 => state7_1784 | 2 => state7_1785 | 3 => state7_1786 | 4 => state7_1787 | 5 => state7_1788 | _ => state7_1789

def stree7RRRRRRLR (i : Nat) : State := match i with | 0 => state7_1790 | 1 => state7_1791 | 2 => state7_1792 | 3 => state7_1793 | 4 => state7_1794 | 5 => state7_1795 | _ => state7_1796

def stree7RRRRRRL (i : Nat) : State := if i < 7 then stree7RRRRRRLL i else stree7RRRRRRLR (i - 7)

def stree7RRRRRRRL (i : Nat) : State := match i with | 0 => state7_1797 | 1 => state7_1798 | 2 => state7_1799 | 3 => state7_1800 | 4 => state7_1801 | 5 => state7_1802 | _ => state7_1803

def stree7RRRRRRRR (i : Nat) : State := match i with | 0 => state7_1804 | 1 => state7_1805 | 2 => state7_1806 | 3 => state7_1807 | 4 => state7_1808 | 5 => state7_1809 | 6 => state7_1810 | _ => state7_1811

def stree7RRRRRRR (i : Nat) : State := if i < 7 then stree7RRRRRRRL i else stree7RRRRRRRR (i - 7)

def stree7RRRRRR (i : Nat) : State := if i < 14 then stree7RRRRRRL i else stree7RRRRRRR (i - 14)

def stree7RRRRR (i : Nat) : State := if i < 28 then stree7RRRRRL i else stree7RRRRRR (i - 28)

def stree7RRRR (i : Nat) : State := if i < 57 then stree7RRRRL i else stree7RRRRR (i - 57)

def stree7RRR (i : Nat) : State := if i < 113 then stree7RRRL i else stree7RRRR (i - 113)

def stree7RR (i : Nat) : State := if i < 226 then stree7RRL i else stree7RRR (i - 226)

def stree7R (i : Nat) : State := if i < 453 then stree7RL i else stree7RR (i - 453)

def stree7 (i : Nat) : State := if i < 906 then stree7L i else stree7R (i - 906)

def ntree7LLLLLLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨3,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩] | 2 => ![⟨6,by decide⟩,⟨7,by decide⟩,⟨8,by decide⟩] | 3 => ![⟨9,by decide⟩,⟨10,by decide⟩,⟨11,by decide⟩] | _ => ![⟨12,by decide⟩,⟨4,by decide⟩,⟨13,by decide⟩]

def ntree7LLLLLLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨14,by decide⟩,⟨15,by decide⟩,⟨16,by decide⟩] | 1 => ![⟨17,by decide⟩,⟨1,by decide⟩,⟨18,by decide⟩] | 2 => ![⟨12,by decide⟩,⟨19,by decide⟩,⟨20,by decide⟩] | 3 => ![⟨21,by decide⟩,⟨22,by decide⟩,⟨23,by decide⟩] | 4 => ![⟨24,by decide⟩,⟨25,by decide⟩,⟨26,by decide⟩] | _ => ![⟨27,by decide⟩,⟨28,by decide⟩,⟨29,by decide⟩]

def ntree7LLLLLL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LLLLLLL i else ntree7LLLLLLR (i - 5)

def ntree7LLLLLRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨30,by decide⟩,⟨31,by decide⟩,⟨8,by decide⟩] | 1 => ![⟨32,by decide⟩,⟨33,by decide⟩,⟨34,by decide⟩] | 2 => ![⟨35,by decide⟩,⟨28,by decide⟩,⟨36,by decide⟩] | 3 => ![⟨37,by decide⟩,⟨38,by decide⟩,⟨16,by decide⟩] | _ => ![⟨39,by decide⟩,⟨25,by decide⟩,⟨40,by decide⟩]

def ntree7LLLLLRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨35,by decide⟩,⟨41,by decide⟩,⟨42,by decide⟩] | 1 => ![⟨43,by decide⟩,⟨44,by decide⟩,⟨23,by decide⟩] | 2 => ![⟨45,by decide⟩,⟨46,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨47,by decide⟩,⟨48,by decide⟩,⟨49,by decide⟩] | 4 => ![⟨30,by decide⟩,⟨50,by decide⟩,⟨51,by decide⟩] | _ => ![⟨52,by decide⟩,⟨53,by decide⟩,⟨11,by decide⟩]

def ntree7LLLLLR (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LLLLLRL i else ntree7LLLLLRR (i - 5)

def ntree7LLLLL (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7LLLLLL i else ntree7LLLLLR (i - 11)

def ntree7LLLLRLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨54,by decide⟩,⟨48,by decide⟩,⟨55,by decide⟩] | 1 => ![⟨37,by decide⟩,⟨56,by decide⟩,⟨57,by decide⟩] | 2 => ![⟨58,by decide⟩,⟨46,by decide⟩,⟨18,by decide⟩] | 3 => ![⟨54,by decide⟩,⟨59,by decide⟩,⟨60,by decide⟩] | _ => ![⟨43,by decide⟩,⟨61,by decide⟩,⟨62,by decide⟩]

def ntree7LLLLRLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨63,by decide⟩,⟨64,by decide⟩,⟨65,by decide⟩] | 1 => ![⟨66,by decide⟩,⟨67,by decide⟩,⟨68,by decide⟩] | 2 => ![⟨69,by decide⟩,⟨70,by decide⟩,⟨71,by decide⟩] | 3 => ![⟨72,by decide⟩,⟨73,by decide⟩,⟨74,by decide⟩] | 4 => ![⟨75,by decide⟩,⟨76,by decide⟩,⟨77,by decide⟩] | _ => ![⟨78,by decide⟩,⟨79,by decide⟩,⟨80,by decide⟩]

def ntree7LLLLRL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LLLLRLL i else ntree7LLLLRLR (i - 5)

def ntree7LLLLRRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨81,by decide⟩,⟨82,by decide⟩,⟨83,by decide⟩] | 1 => ![⟨84,by decide⟩,⟨85,by decide⟩,⟨86,by decide⟩] | 2 => ![⟨87,by decide⟩,⟨88,by decide⟩,⟨89,by decide⟩] | 3 => ![⟨25,by decide⟩,⟨25,by decide⟩,⟨90,by decide⟩] | 4 => ![⟨91,by decide⟩,⟨92,by decide⟩,⟨93,by decide⟩] | _ => ![⟨94,by decide⟩,⟨95,by decide⟩,⟨96,by decide⟩]

def ntree7LLLLRRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨35,by decide⟩,⟨97,by decide⟩,⟨98,by decide⟩] | 1 => ![⟨99,by decide⟩,⟨100,by decide⟩,⟨101,by decide⟩] | 2 => ![⟨102,by decide⟩,⟨103,by decide⟩,⟨104,by decide⟩] | 3 => ![⟨39,by decide⟩,⟨105,by decide⟩,⟨106,by decide⟩] | 4 => ![⟨107,by decide⟩,⟨108,by decide⟩,⟨109,by decide⟩] | _ => ![⟨110,by decide⟩,⟨111,by decide⟩,⟨112,by decide⟩]

def ntree7LLLLRR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7LLLLRRL i else ntree7LLLLRRR (i - 6)

def ntree7LLLLR (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7LLLLRL i else ntree7LLLLRR (i - 11)

def ntree7LLLL (i : Nat) : Fin 3 → Fin 1812 := if i < 22 then ntree7LLLLL i else ntree7LLLLR (i - 22)

def ntree7LLLRLLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨113,by decide⟩,⟨114,by decide⟩,⟨115,by decide⟩] | 1 => ![⟨116,by decide⟩,⟨117,by decide⟩,⟨118,by decide⟩] | 2 => ![⟨119,by decide⟩,⟨120,by decide⟩,⟨121,by decide⟩] | 3 => ![⟨122,by decide⟩,⟨123,by decide⟩,⟨124,by decide⟩] | _ => ![⟨125,by decide⟩,⟨126,by decide⟩,⟨127,by decide⟩]

def ntree7LLLRLLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨128,by decide⟩,⟨129,by decide⟩,⟨130,by decide⟩] | 1 => ![⟨43,by decide⟩,⟨131,by decide⟩,⟨132,by decide⟩] | 2 => ![⟨133,by decide⟩,⟨134,by decide⟩,⟨135,by decide⟩] | 3 => ![⟨136,by decide⟩,⟨137,by decide⟩,⟨138,by decide⟩] | 4 => ![⟨139,by decide⟩,⟨140,by decide⟩,⟨141,by decide⟩] | _ => ![⟨142,by decide⟩,⟨143,by decide⟩,⟨144,by decide⟩]

def ntree7LLLRLL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LLLRLLL i else ntree7LLLRLLR (i - 5)

def ntree7LLLRLRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨145,by decide⟩,⟨146,by decide⟩,⟨147,by decide⟩] | 1 => ![⟨11,by decide⟩,⟨148,by decide⟩,⟨11,by decide⟩] | 2 => ![⟨149,by decide⟩,⟨150,by decide⟩,⟨151,by decide⟩] | 3 => ![⟨152,by decide⟩,⟨153,by decide⟩,⟨154,by decide⟩] | 4 => ![⟨155,by decide⟩,⟨156,by decide⟩,⟨157,by decide⟩] | _ => ![⟨158,by decide⟩,⟨159,by decide⟩,⟨160,by decide⟩]

def ntree7LLLRLRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨161,by decide⟩,⟨162,by decide⟩,⟨163,by decide⟩] | 1 => ![⟨164,by decide⟩,⟨165,by decide⟩,⟨166,by decide⟩] | 2 => ![⟨167,by decide⟩,⟨168,by decide⟩,⟨169,by decide⟩] | 3 => ![⟨170,by decide⟩,⟨171,by decide⟩,⟨172,by decide⟩] | 4 => ![⟨37,by decide⟩,⟨173,by decide⟩,⟨174,by decide⟩] | _ => ![⟨175,by decide⟩,⟨176,by decide⟩,⟨177,by decide⟩]

def ntree7LLLRLR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7LLLRLRL i else ntree7LLLRLRR (i - 6)

def ntree7LLLRL (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7LLLRLL i else ntree7LLLRLR (i - 11)

def ntree7LLLRRLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨178,by decide⟩,⟨179,by decide⟩,⟨180,by decide⟩] | 1 => ![⟨181,by decide⟩,⟨182,by decide⟩,⟨183,by decide⟩] | 2 => ![⟨184,by decide⟩,⟨185,by decide⟩,⟨186,by decide⟩] | 3 => ![⟨187,by decide⟩,⟨188,by decide⟩,⟨189,by decide⟩] | _ => ![⟨190,by decide⟩,⟨191,by decide⟩,⟨192,by decide⟩]

def ntree7LLLRRLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨193,by decide⟩,⟨194,by decide⟩,⟨195,by decide⟩] | 1 => ![⟨196,by decide⟩,⟨197,by decide⟩,⟨198,by decide⟩] | 2 => ![⟨52,by decide⟩,⟨199,by decide⟩,⟨200,by decide⟩] | 3 => ![⟨201,by decide⟩,⟨202,by decide⟩,⟨203,by decide⟩] | 4 => ![⟨204,by decide⟩,⟨205,by decide⟩,⟨206,by decide⟩] | _ => ![⟨54,by decide⟩,⟨207,by decide⟩,⟨208,by decide⟩]

def ntree7LLLRRL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LLLRRLL i else ntree7LLLRRLR (i - 5)

def ntree7LLLRRRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨209,by decide⟩,⟨210,by decide⟩,⟨211,by decide⟩] | 1 => ![⟨212,by decide⟩,⟨213,by decide⟩,⟨214,by decide⟩] | 2 => ![⟨1,by decide⟩,⟨215,by decide⟩,⟨216,by decide⟩] | 3 => ![⟨217,by decide⟩,⟨218,by decide⟩,⟨219,by decide⟩] | 4 => ![⟨220,by decide⟩,⟨221,by decide⟩,⟨222,by decide⟩] | _ => ![⟨12,by decide⟩,⟨223,by decide⟩,⟨224,by decide⟩]

def ntree7LLLRRRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨12,by decide⟩,⟨225,by decide⟩,⟨226,by decide⟩] | 1 => ![⟨227,by decide⟩,⟨228,by decide⟩,⟨229,by decide⟩] | 2 => ![⟨17,by decide⟩,⟨230,by decide⟩,⟨231,by decide⟩] | 3 => ![⟨232,by decide⟩,⟨233,by decide⟩,⟨234,by decide⟩] | 4 => ![⟨235,by decide⟩,⟨236,by decide⟩,⟨237,by decide⟩] | _ => ![⟨238,by decide⟩,⟨239,by decide⟩,⟨240,by decide⟩]

def ntree7LLLRRR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7LLLRRRL i else ntree7LLLRRRR (i - 6)

def ntree7LLLRR (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7LLLRRL i else ntree7LLLRRR (i - 11)

def ntree7LLLR (i : Nat) : Fin 3 → Fin 1812 := if i < 23 then ntree7LLLRL i else ntree7LLLRR (i - 23)

def ntree7LLL (i : Nat) : Fin 3 → Fin 1812 := if i < 45 then ntree7LLLL i else ntree7LLLR (i - 45)

def ntree7LLRLLLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨241,by decide⟩,⟨242,by decide⟩,⟨243,by decide⟩] | 1 => ![⟨244,by decide⟩,⟨245,by decide⟩,⟨246,by decide⟩] | 2 => ![⟨247,by decide⟩,⟨248,by decide⟩,⟨249,by decide⟩] | 3 => ![⟨250,by decide⟩,⟨251,by decide⟩,⟨252,by decide⟩] | _ => ![⟨253,by decide⟩,⟨254,by decide⟩,⟨255,by decide⟩]

def ntree7LLRLLLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨81,by decide⟩,⟨256,by decide⟩,⟨257,by decide⟩] | 1 => ![⟨258,by decide⟩,⟨259,by decide⟩,⟨260,by decide⟩] | 2 => ![⟨261,by decide⟩,⟨262,by decide⟩,⟨263,by decide⟩] | 3 => ![⟨264,by decide⟩,⟨265,by decide⟩,⟨266,by decide⟩] | 4 => ![⟨267,by decide⟩,⟨268,by decide⟩,⟨269,by decide⟩] | _ => ![⟨270,by decide⟩,⟨271,by decide⟩,⟨272,by decide⟩]

def ntree7LLRLLL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LLRLLLL i else ntree7LLRLLLR (i - 5)

def ntree7LLRLLRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨273,by decide⟩,⟨274,by decide⟩,⟨275,by decide⟩] | 1 => ![⟨276,by decide⟩,⟨277,by decide⟩,⟨278,by decide⟩] | 2 => ![⟨279,by decide⟩,⟨280,by decide⟩,⟨281,by decide⟩] | 3 => ![⟨18,by decide⟩,⟨282,by decide⟩,⟨283,by decide⟩] | _ => ![⟨284,by decide⟩,⟨285,by decide⟩,⟨286,by decide⟩]

def ntree7LLRLLRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨287,by decide⟩,⟨288,by decide⟩,⟨289,by decide⟩] | 1 => ![⟨290,by decide⟩,⟨291,by decide⟩,⟨292,by decide⟩] | 2 => ![⟨293,by decide⟩,⟨294,by decide⟩,⟨295,by decide⟩] | 3 => ![⟨296,by decide⟩,⟨297,by decide⟩,⟨298,by decide⟩] | 4 => ![⟨299,by decide⟩,⟨300,by decide⟩,⟨301,by decide⟩] | _ => ![⟨302,by decide⟩,⟨303,by decide⟩,⟨304,by decide⟩]

def ntree7LLRLLR (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LLRLLRL i else ntree7LLRLLRR (i - 5)

def ntree7LLRLL (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7LLRLLL i else ntree7LLRLLR (i - 11)

def ntree7LLRLRLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨305,by decide⟩,⟨306,by decide⟩,⟨307,by decide⟩] | 1 => ![⟨308,by decide⟩,⟨309,by decide⟩,⟨310,by decide⟩] | 2 => ![⟨311,by decide⟩,⟨312,by decide⟩,⟨313,by decide⟩] | 3 => ![⟨314,by decide⟩,⟨315,by decide⟩,⟨316,by decide⟩] | _ => ![⟨290,by decide⟩,⟨317,by decide⟩,⟨318,by decide⟩]

def ntree7LLRLRLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨319,by decide⟩,⟨320,by decide⟩,⟨321,by decide⟩] | 1 => ![⟨322,by decide⟩,⟨323,by decide⟩,⟨324,by decide⟩] | 2 => ![⟨299,by decide⟩,⟨325,by decide⟩,⟨326,by decide⟩] | 3 => ![⟨327,by decide⟩,⟨328,by decide⟩,⟨329,by decide⟩] | 4 => ![⟨330,by decide⟩,⟨331,by decide⟩,⟨332,by decide⟩] | _ => ![⟨308,by decide⟩,⟨333,by decide⟩,⟨334,by decide⟩]

def ntree7LLRLRL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LLRLRLL i else ntree7LLRLRLR (i - 5)

def ntree7LLRLRRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨335,by decide⟩,⟨336,by decide⟩,⟨337,by decide⟩] | 1 => ![⟨338,by decide⟩,⟨339,by decide⟩,⟨340,by decide⟩] | 2 => ![⟨341,by decide⟩,⟨342,by decide⟩,⟨318,by decide⟩] | 3 => ![⟨343,by decide⟩,⟨344,by decide⟩,⟨345,by decide⟩] | 4 => ![⟨296,by decide⟩,⟨346,by decide⟩,⟨347,by decide⟩] | _ => ![⟨348,by decide⟩,⟨349,by decide⟩,⟨326,by decide⟩]

def ntree7LLRLRRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨350,by decide⟩,⟨351,by decide⟩,⟨352,by decide⟩] | 1 => ![⟨305,by decide⟩,⟨353,by decide⟩,⟨354,by decide⟩] | 2 => ![⟨355,by decide⟩,⟨356,by decide⟩,⟨334,by decide⟩] | 3 => ![⟨357,by decide⟩,⟨358,by decide⟩,⟨359,by decide⟩] | 4 => ![⟨314,by decide⟩,⟨360,by decide⟩,⟨361,by decide⟩] | _ => ![⟨362,by decide⟩,⟨363,by decide⟩,⟨364,by decide⟩]

def ntree7LLRLRR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7LLRLRRL i else ntree7LLRLRRR (i - 6)

def ntree7LLRLR (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7LLRLRL i else ntree7LLRLRR (i - 11)

def ntree7LLRL (i : Nat) : Fin 3 → Fin 1812 := if i < 22 then ntree7LLRLL i else ntree7LLRLR (i - 22)

def ntree7LLRRLLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨365,by decide⟩,⟨366,by decide⟩,⟨367,by decide⟩] | 1 => ![⟨368,by decide⟩,⟨369,by decide⟩,⟨295,by decide⟩] | 2 => ![⟨370,by decide⟩,⟨371,by decide⟩,⟨372,by decide⟩] | 3 => ![⟨373,by decide⟩,⟨374,by decide⟩,⟨375,by decide⟩] | _ => ![⟨376,by decide⟩,⟨377,by decide⟩,⟨304,by decide⟩]

def ntree7LLRRLLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨378,by decide⟩,⟨379,by decide⟩,⟨372,by decide⟩] | 1 => ![⟨380,by decide⟩,⟨381,by decide⟩,⟨382,by decide⟩] | 2 => ![⟨383,by decide⟩,⟨384,by decide⟩,⟨313,by decide⟩] | 3 => ![⟨385,by decide⟩,⟨386,by decide⟩,⟨387,by decide⟩] | 4 => ![⟨388,by decide⟩,⟨389,by decide⟩,⟨390,by decide⟩] | _ => ![⟨391,by decide⟩,⟨392,by decide⟩,⟨321,by decide⟩]

def ntree7LLRRLL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LLRRLLL i else ntree7LLRRLLR (i - 5)

def ntree7LLRRLRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨393,by decide⟩,⟨394,by decide⟩,⟨395,by decide⟩] | 1 => ![⟨396,by decide⟩,⟨397,by decide⟩,⟨398,by decide⟩] | 2 => ![⟨399,by decide⟩,⟨400,by decide⟩,⟨329,by decide⟩] | 3 => ![⟨401,by decide⟩,⟨402,by decide⟩,⟨395,by decide⟩] | 4 => ![⟨403,by decide⟩,⟨404,by decide⟩,⟨405,by decide⟩] | _ => ![⟨406,by decide⟩,⟨407,by decide⟩,⟨337,by decide⟩]

def ntree7LLRRLRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨408,by decide⟩,⟨409,by decide⟩,⟨410,by decide⟩] | 1 => ![⟨365,by decide⟩,⟨411,by decide⟩,⟨412,by decide⟩] | 2 => ![⟨413,by decide⟩,⟨414,by decide⟩,⟨345,by decide⟩] | 3 => ![⟨415,by decide⟩,⟨416,by decide⟩,⟨417,by decide⟩] | 4 => ![⟨373,by decide⟩,⟨418,by decide⟩,⟨419,by decide⟩] | _ => ![⟨420,by decide⟩,⟨421,by decide⟩,⟨352,by decide⟩]

def ntree7LLRRLR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7LLRRLRL i else ntree7LLRRLRR (i - 6)

def ntree7LLRRL (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7LLRRLL i else ntree7LLRRLR (i - 11)

def ntree7LLRRRLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨422,by decide⟩,⟨423,by decide⟩,⟨417,by decide⟩] | 1 => ![⟨380,by decide⟩,⟨424,by decide⟩,⟨425,by decide⟩] | 2 => ![⟨426,by decide⟩,⟨427,by decide⟩,⟨359,by decide⟩] | 3 => ![⟨2,by decide⟩,⟨428,by decide⟩,⟨429,by decide⟩] | _ => ![⟨430,by decide⟩,⟨431,by decide⟩,⟨432,by decide⟩]

def ntree7LLRRRLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨433,by decide⟩,⟨434,by decide⟩,⟨435,by decide⟩] | 1 => ![⟨436,by decide⟩,⟨437,by decide⟩,⟨438,by decide⟩] | 2 => ![⟨439,by decide⟩,⟨440,by decide⟩,⟨441,by decide⟩] | 3 => ![⟨442,by decide⟩,⟨443,by decide⟩,⟨444,by decide⟩] | 4 => ![⟨445,by decide⟩,⟨446,by decide⟩,⟨447,by decide⟩] | _ => ![⟨448,by decide⟩,⟨449,by decide⟩,⟨450,by decide⟩]

def ntree7LLRRRL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LLRRRLL i else ntree7LLRRRLR (i - 5)

def ntree7LLRRRRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨451,by decide⟩,⟨452,by decide⟩,⟨453,by decide⟩] | 1 => ![⟨30,by decide⟩,⟨454,by decide⟩,⟨455,by decide⟩] | 2 => ![⟨456,by decide⟩,⟨457,by decide⟩,⟨458,by decide⟩] | 3 => ![⟨30,by decide⟩,⟨459,by decide⟩,⟨460,by decide⟩] | 4 => ![⟨461,by decide⟩,⟨462,by decide⟩,⟨463,by decide⟩] | _ => ![⟨464,by decide⟩,⟨465,by decide⟩,⟨466,by decide⟩]

def ntree7LLRRRRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨467,by decide⟩,⟨468,by decide⟩,⟨469,by decide⟩] | 1 => ![⟨470,by decide⟩,⟨471,by decide⟩,⟨472,by decide⟩] | 2 => ![⟨473,by decide⟩,⟨474,by decide⟩,⟨475,by decide⟩] | 3 => ![⟨476,by decide⟩,⟨477,by decide⟩,⟨478,by decide⟩] | 4 => ![⟨45,by decide⟩,⟨479,by decide⟩,⟨480,by decide⟩] | _ => ![⟨481,by decide⟩,⟨482,by decide⟩,⟨483,by decide⟩]

def ntree7LLRRRR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7LLRRRRL i else ntree7LLRRRRR (i - 6)

def ntree7LLRRR (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7LLRRRL i else ntree7LLRRRR (i - 11)

def ntree7LLRR (i : Nat) : Fin 3 → Fin 1812 := if i < 23 then ntree7LLRRL i else ntree7LLRRR (i - 23)

def ntree7LLR (i : Nat) : Fin 3 → Fin 1812 := if i < 45 then ntree7LLRL i else ntree7LLRR (i - 45)

def ntree7LL (i : Nat) : Fin 3 → Fin 1812 := if i < 91 then ntree7LLL i else ntree7LLR (i - 91)

def ntree7LRLLLLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨484,by decide⟩,⟨485,by decide⟩,⟨486,by decide⟩] | 1 => ![⟨190,by decide⟩,⟨487,by decide⟩,⟨488,by decide⟩] | 2 => ![⟨489,by decide⟩,⟨490,by decide⟩,⟨491,by decide⟩] | 3 => ![⟨492,by decide⟩,⟨493,by decide⟩,⟨494,by decide⟩] | _ => ![⟨46,by decide⟩,⟨495,by decide⟩,⟨496,by decide⟩]

def ntree7LRLLLLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨497,by decide⟩,⟨498,by decide⟩,⟨499,by decide⟩] | 1 => ![⟨500,by decide⟩,⟨501,by decide⟩,⟨502,by decide⟩] | 2 => ![⟨503,by decide⟩,⟨504,by decide⟩,⟨505,by decide⟩] | 3 => ![⟨506,by decide⟩,⟨507,by decide⟩,⟨508,by decide⟩] | 4 => ![⟨509,by decide⟩,⟨510,by decide⟩,⟨297,by decide⟩] | _ => ![⟨511,by decide⟩,⟨512,by decide⟩,⟨513,by decide⟩]

def ntree7LRLLLL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LRLLLLL i else ntree7LRLLLLR (i - 5)

def ntree7LRLLLRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨514,by decide⟩,⟨515,by decide⟩,⟨516,by decide⟩] | 1 => ![⟨517,by decide⟩,⟨518,by decide⟩,⟨306,by decide⟩] | 2 => ![⟨519,by decide⟩,⟨520,by decide⟩,⟨521,by decide⟩] | 3 => ![⟨522,by decide⟩,⟨523,by decide⟩,⟨524,by decide⟩] | _ => ![⟨509,by decide⟩,⟨525,by decide⟩,⟨315,by decide⟩]

def ntree7LRLLLRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨526,by decide⟩,⟨527,by decide⟩,⟨528,by decide⟩] | 1 => ![⟨529,by decide⟩,⟨530,by decide⟩,⟨531,by decide⟩] | 2 => ![⟨532,by decide⟩,⟨533,by decide⟩,⟨323,by decide⟩] | 3 => ![⟨534,by decide⟩,⟨535,by decide⟩,⟨536,by decide⟩] | 4 => ![⟨537,by decide⟩,⟨538,by decide⟩,⟨539,by decide⟩] | _ => ![⟨540,by decide⟩,⟨541,by decide⟩,⟨331,by decide⟩]

def ntree7LRLLLR (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LRLLLRL i else ntree7LRLLLRR (i - 5)

def ntree7LRLLL (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7LRLLLL i else ntree7LRLLLR (i - 11)

def ntree7LRLLRLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨542,by decide⟩,⟨543,by decide⟩,⟨544,by decide⟩] | 1 => ![⟨545,by decide⟩,⟨546,by decide⟩,⟨547,by decide⟩] | 2 => ![⟨532,by decide⟩,⟨548,by decide⟩,⟨339,by decide⟩] | 3 => ![⟨549,by decide⟩,⟨527,by decide⟩,⟨550,by decide⟩] | _ => ![⟨551,by decide⟩,⟨552,by decide⟩,⟨553,by decide⟩]

def ntree7LRLLRLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨554,by decide⟩,⟨555,by decide⟩,⟨346,by decide⟩] | 1 => ![⟨556,by decide⟩,⟨535,by decide⟩,⟨557,by decide⟩] | 2 => ![⟨558,by decide⟩,⟨559,by decide⟩,⟨560,by decide⟩] | 3 => ![⟨561,by decide⟩,⟨562,by decide⟩,⟨353,by decide⟩] | 4 => ![⟨563,by decide⟩,⟨543,by decide⟩,⟨564,by decide⟩] | _ => ![⟨565,by decide⟩,⟨566,by decide⟩,⟨567,by decide⟩]

def ntree7LRLLRL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LRLLRLL i else ntree7LRLLRLR (i - 5)

def ntree7LRLLRRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨554,by decide⟩,⟨568,by decide⟩,⟨360,by decide⟩] | 1 => ![⟨569,by decide⟩,⟨570,by decide⟩,⟨571,by decide⟩] | 2 => ![⟨572,by decide⟩,⟨573,by decide⟩,⟨366,by decide⟩] | 3 => ![⟨574,by decide⟩,⟨507,by decide⟩,⟨575,by decide⟩] | 4 => ![⟨569,by decide⟩,⟨576,by decide⟩,⟨577,by decide⟩] | _ => ![⟨578,by decide⟩,⟨579,by decide⟩,⟨374,by decide⟩]

def ntree7LRLLRRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨580,by decide⟩,⟨515,by decide⟩,⟨581,by decide⟩] | 1 => ![⟨582,by decide⟩,⟨576,by decide⟩,⟨583,by decide⟩] | 2 => ![⟨572,by decide⟩,⟨584,by decide⟩,⟨381,by decide⟩] | 3 => ![⟨585,by decide⟩,⟨523,by decide⟩,⟨586,by decide⟩] | 4 => ![⟨587,by decide⟩,⟨588,by decide⟩,⟨589,by decide⟩] | _ => ![⟨590,by decide⟩,⟨591,by decide⟩,⟨389,by decide⟩]

def ntree7LRLLRR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7LRLLRRL i else ntree7LRLLRRR (i - 6)

def ntree7LRLLR (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7LRLLRL i else ntree7LRLLRR (i - 11)

def ntree7LRLL (i : Nat) : Fin 3 → Fin 1812 := if i < 22 then ntree7LRLLL i else ntree7LRLLR (i - 22)

def ntree7LRLRLLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨592,by decide⟩,⟨530,by decide⟩,⟨593,by decide⟩] | 1 => ![⟨587,by decide⟩,⟨594,by decide⟩,⟨595,by decide⟩] | 2 => ![⟨596,by decide⟩,⟨597,by decide⟩,⟨397,by decide⟩] | 3 => ![⟨598,by decide⟩,⟨538,by decide⟩,⟨599,by decide⟩] | _ => ![⟨600,by decide⟩,⟨594,by decide⟩,⟨601,by decide⟩]

def ntree7LRLRLLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨590,by decide⟩,⟨602,by decide⟩,⟨404,by decide⟩] | 1 => ![⟨603,by decide⟩,⟨546,by decide⟩,⟨604,by decide⟩] | 2 => ![⟨605,by decide⟩,⟨606,by decide⟩,⟨607,by decide⟩] | 3 => ![⟨608,by decide⟩,⟨609,by decide⟩,⟨411,by decide⟩] | 4 => ![⟨610,by decide⟩,⟨552,by decide⟩,⟨611,by decide⟩] | _ => ![⟨605,by decide⟩,⟨612,by decide⟩,⟨613,by decide⟩]

def ntree7LRLRLL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LRLRLLL i else ntree7LRLRLLR (i - 5)

def ntree7LRLRLRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨614,by decide⟩,⟨615,by decide⟩,⟨418,by decide⟩] | 1 => ![⟨616,by decide⟩,⟨559,by decide⟩,⟨617,by decide⟩] | 2 => ![⟨618,by decide⟩,⟨612,by decide⟩,⟨619,by decide⟩] | 3 => ![⟨608,by decide⟩,⟨620,by decide⟩,⟨424,by decide⟩] | 4 => ![⟨621,by decide⟩,⟨566,by decide⟩,⟨622,by decide⟩] | _ => ![⟨623,by decide⟩,⟨624,by decide⟩,⟨625,by decide⟩]

def ntree7LRLRLRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨626,by decide⟩,⟨627,by decide⟩,⟨628,by decide⟩] | 1 => ![⟨629,by decide⟩,⟨630,by decide⟩,⟨631,by decide⟩] | 2 => ![⟨632,by decide⟩,⟨633,by decide⟩,⟨634,by decide⟩] | 3 => ![⟨635,by decide⟩,⟨627,by decide⟩,⟨636,by decide⟩] | 4 => ![⟨637,by decide⟩,⟨638,by decide⟩,⟨639,by decide⟩] | _ => ![⟨640,by decide⟩,⟨624,by decide⟩,⟨641,by decide⟩]

def ntree7LRLRLR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7LRLRLRL i else ntree7LRLRLRR (i - 6)

def ntree7LRLRL (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7LRLRLL i else ntree7LRLRLR (i - 11)

def ntree7LRLRRLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨635,by decide⟩,⟨642,by decide⟩,⟨643,by decide⟩] | 1 => ![⟨644,by decide⟩,⟨645,by decide⟩,⟨646,by decide⟩] | 2 => ![⟨647,by decide⟩,⟨648,by decide⟩,⟨649,by decide⟩] | 3 => ![⟨650,by decide⟩,⟨651,by decide⟩,⟨652,by decide⟩] | _ => ![⟨653,by decide⟩,⟨654,by decide⟩,⟨631,by decide⟩]

def ntree7LRLRRLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨655,by decide⟩,⟨656,by decide⟩,⟨657,by decide⟩] | 1 => ![⟨658,by decide⟩,⟨651,by decide⟩,⟨659,by decide⟩] | 2 => ![⟨660,by decide⟩,⟨661,by decide⟩,⟨639,by decide⟩] | 3 => ![⟨662,by decide⟩,⟨648,by decide⟩,⟨663,by decide⟩] | 4 => ![⟨658,by decide⟩,⟨664,by decide⟩,⟨665,by decide⟩] | _ => ![⟨666,by decide⟩,⟨667,by decide⟩,⟨646,by decide⟩]

def ntree7LRLRRL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LRLRRLL i else ntree7LRLRRLR (i - 5)

def ntree7LRLRRRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨668,by decide⟩,⟨669,by decide⟩,⟨625,by decide⟩] | 1 => ![⟨670,by decide⟩,⟨671,by decide⟩,⟨672,by decide⟩] | 2 => ![⟨653,by decide⟩,⟨673,by decide⟩,⟨674,by decide⟩] | 3 => ![⟨675,by decide⟩,⟨676,by decide⟩,⟨634,by decide⟩] | 4 => ![⟨677,by decide⟩,⟨671,by decide⟩,⟨678,by decide⟩] | _ => ![⟨660,by decide⟩,⟨679,by decide⟩,⟨680,by decide⟩]

def ntree7LRLRRRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨681,by decide⟩,⟨669,by decide⟩,⟨641,by decide⟩] | 1 => ![⟨677,by decide⟩,⟨682,by decide⟩,⟨683,by decide⟩] | 2 => ![⟨666,by decide⟩,⟨684,by decide⟩,⟨685,by decide⟩] | 3 => ![⟨686,by decide⟩,⟨687,by decide⟩,⟨688,by decide⟩] | 4 => ![⟨689,by decide⟩,⟨690,by decide⟩,⟨691,by decide⟩] | _ => ![⟨692,by decide⟩,⟨693,by decide⟩,⟨694,by decide⟩]

def ntree7LRLRRR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7LRLRRRL i else ntree7LRLRRRR (i - 6)

def ntree7LRLRR (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7LRLRRL i else ntree7LRLRRR (i - 11)

def ntree7LRLR (i : Nat) : Fin 3 → Fin 1812 := if i < 23 then ntree7LRLRL i else ntree7LRLRR (i - 23)

def ntree7LRL (i : Nat) : Fin 3 → Fin 1812 := if i < 45 then ntree7LRLL i else ntree7LRLR (i - 45)

def ntree7LRRLLLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨695,by decide⟩,⟨696,by decide⟩,⟨697,by decide⟩] | 1 => ![⟨698,by decide⟩,⟨699,by decide⟩,⟨700,by decide⟩] | 2 => ![⟨701,by decide⟩,⟨702,by decide⟩,⟨703,by decide⟩] | 3 => ![⟨704,by decide⟩,⟨705,by decide⟩,⟨706,by decide⟩] | _ => ![⟨707,by decide⟩,⟨708,by decide⟩,⟨709,by decide⟩]

def ntree7LRRLLLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨710,by decide⟩,⟨711,by decide⟩,⟨712,by decide⟩] | 1 => ![⟨713,by decide⟩,⟨714,by decide⟩,⟨715,by decide⟩] | 2 => ![⟨716,by decide⟩,⟨717,by decide⟩,⟨718,by decide⟩] | 3 => ![⟨719,by decide⟩,⟨720,by decide⟩,⟨721,by decide⟩] | 4 => ![⟨722,by decide⟩,⟨723,by decide⟩,⟨724,by decide⟩] | _ => ![⟨725,by decide⟩,⟨726,by decide⟩,⟨727,by decide⟩]

def ntree7LRRLLL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LRRLLLL i else ntree7LRRLLLR (i - 5)

def ntree7LRRLLRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨728,by decide⟩,⟨729,by decide⟩,⟨730,by decide⟩] | 1 => ![⟨731,by decide⟩,⟨732,by decide⟩,⟨733,by decide⟩] | 2 => ![⟨734,by decide⟩,⟨735,by decide⟩,⟨736,by decide⟩] | 3 => ![⟨737,by decide⟩,⟨738,by decide⟩,⟨739,by decide⟩] | _ => ![⟨740,by decide⟩,⟨741,by decide⟩,⟨742,by decide⟩]

def ntree7LRRLLRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨743,by decide⟩,⟨744,by decide⟩,⟨745,by decide⟩] | 1 => ![⟨746,by decide⟩,⟨747,by decide⟩,⟨748,by decide⟩] | 2 => ![⟨749,by decide⟩,⟨750,by decide⟩,⟨751,by decide⟩] | 3 => ![⟨752,by decide⟩,⟨753,by decide⟩,⟨754,by decide⟩] | 4 => ![⟨755,by decide⟩,⟨756,by decide⟩,⟨757,by decide⟩] | _ => ![⟨758,by decide⟩,⟨759,by decide⟩,⟨760,by decide⟩]

def ntree7LRRLLR (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LRRLLRL i else ntree7LRRLLRR (i - 5)

def ntree7LRRLL (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7LRRLLL i else ntree7LRRLLR (i - 11)

def ntree7LRRLRLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨761,by decide⟩,⟨762,by decide⟩,⟨763,by decide⟩] | 1 => ![⟨764,by decide⟩,⟨765,by decide⟩,⟨766,by decide⟩] | 2 => ![⟨767,by decide⟩,⟨768,by decide⟩,⟨769,by decide⟩] | 3 => ![⟨770,by decide⟩,⟨771,by decide⟩,⟨772,by decide⟩] | _ => ![⟨773,by decide⟩,⟨774,by decide⟩,⟨775,by decide⟩]

def ntree7LRRLRLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨776,by decide⟩,⟨777,by decide⟩,⟨11,by decide⟩] | 1 => ![⟨778,by decide⟩,⟨779,by decide⟩,⟨780,by decide⟩] | 2 => ![⟨781,by decide⟩,⟨782,by decide⟩,⟨783,by decide⟩] | 3 => ![⟨784,by decide⟩,⟨785,by decide⟩,⟨786,by decide⟩] | 4 => ![⟨787,by decide⟩,⟨788,by decide⟩,⟨789,by decide⟩] | _ => ![⟨790,by decide⟩,⟨791,by decide⟩,⟨792,by decide⟩]

def ntree7LRRLRL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LRRLRLL i else ntree7LRRLRLR (i - 5)

def ntree7LRRLRRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨793,by decide⟩,⟨794,by decide⟩,⟨795,by decide⟩] | 1 => ![⟨796,by decide⟩,⟨797,by decide⟩,⟨798,by decide⟩] | 2 => ![⟨799,by decide⟩,⟨800,by decide⟩,⟨801,by decide⟩] | 3 => ![⟨802,by decide⟩,⟨803,by decide⟩,⟨174,by decide⟩] | 4 => ![⟨804,by decide⟩,⟨805,by decide⟩,⟨806,by decide⟩] | _ => ![⟨807,by decide⟩,⟨808,by decide⟩,⟨809,by decide⟩]

def ntree7LRRLRRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨810,by decide⟩,⟨811,by decide⟩,⟨812,by decide⟩] | 1 => ![⟨813,by decide⟩,⟨814,by decide⟩,⟨815,by decide⟩] | 2 => ![⟨816,by decide⟩,⟨817,by decide⟩,⟨818,by decide⟩] | 3 => ![⟨819,by decide⟩,⟨820,by decide⟩,⟨192,by decide⟩] | 4 => ![⟨821,by decide⟩,⟨822,by decide⟩,⟨823,by decide⟩] | _ => ![⟨824,by decide⟩,⟨825,by decide⟩,⟨826,by decide⟩]

def ntree7LRRLRR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7LRRLRRL i else ntree7LRRLRRR (i - 6)

def ntree7LRRLR (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7LRRLRL i else ntree7LRRLRR (i - 11)

def ntree7LRRL (i : Nat) : Fin 3 → Fin 1812 := if i < 22 then ntree7LRRLL i else ntree7LRRLR (i - 22)

def ntree7LRRRLLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨827,by decide⟩,⟨828,by decide⟩,⟨200,by decide⟩] | 1 => ![⟨829,by decide⟩,⟨830,by decide⟩,⟨208,by decide⟩] | 2 => ![⟨831,by decide⟩,⟨832,by decide⟩,⟨174,by decide⟩] | 3 => ![⟨833,by decide⟩,⟨834,by decide⟩,⟨208,by decide⟩] | _ => ![⟨835,by decide⟩,⟨836,by decide⟩,⟨837,by decide⟩]

def ntree7LRRRLLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨838,by decide⟩,⟨839,by decide⟩,⟨840,by decide⟩] | 1 => ![⟨841,by decide⟩,⟨842,by decide⟩,⟨843,by decide⟩] | 2 => ![⟨217,by decide⟩,⟨844,by decide⟩,⟨845,by decide⟩] | 3 => ![⟨846,by decide⟩,⟨847,by decide⟩,⟨848,by decide⟩] | 4 => ![⟨849,by decide⟩,⟨850,by decide⟩,⟨851,by decide⟩] | _ => ![⟨12,by decide⟩,⟨852,by decide⟩,⟨780,by decide⟩]

def ntree7LRRRLL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LRRRLLL i else ntree7LRRRLLR (i - 5)

def ntree7LRRRLRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨853,by decide⟩,⟨854,by decide⟩,⟨855,by decide⟩] | 1 => ![⟨856,by decide⟩,⟨857,by decide⟩,⟨858,by decide⟩] | 2 => ![⟨232,by decide⟩,⟨217,by decide⟩,⟨284,by decide⟩] | 3 => ![⟨859,by decide⟩,⟨860,by decide⟩,⟨861,by decide⟩] | 4 => ![⟨862,by decide⟩,⟨863,by decide⟩,⟨864,by decide⟩] | _ => ![⟨865,by decide⟩,⟨866,by decide⟩,⟨867,by decide⟩]

def ntree7LRRRLRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨868,by decide⟩,⟨869,by decide⟩,⟨870,by decide⟩] | 1 => ![⟨871,by decide⟩,⟨872,by decide⟩,⟨873,by decide⟩] | 2 => ![⟨874,by decide⟩,⟨875,by decide⟩,⟨876,by decide⟩] | 3 => ![⟨877,by decide⟩,⟨878,by decide⟩,⟨879,by decide⟩] | 4 => ![⟨880,by decide⟩,⟨881,by decide⟩,⟨882,by decide⟩] | _ => ![⟨258,by decide⟩,⟨883,by decide⟩,⟨884,by decide⟩]

def ntree7LRRRLR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7LRRRLRL i else ntree7LRRRLRR (i - 6)

def ntree7LRRRL (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7LRRRLL i else ntree7LRRRLR (i - 11)

def ntree7LRRRRLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨885,by decide⟩,⟨886,by decide⟩,⟨887,by decide⟩] | 1 => ![⟨888,by decide⟩,⟨889,by decide⟩,⟨890,by decide⟩] | 2 => ![⟨891,by decide⟩,⟨892,by decide⟩,⟨893,by decide⟩] | 3 => ![⟨894,by decide⟩,⟨895,by decide⟩,⟨896,by decide⟩] | _ => ![⟨897,by decide⟩,⟨898,by decide⟩,⟨899,by decide⟩]

def ntree7LRRRRLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨900,by decide⟩,⟨901,by decide⟩,⟨902,by decide⟩] | 1 => ![⟨903,by decide⟩,⟨904,by decide⟩,⟨905,by decide⟩] | 2 => ![⟨906,by decide⟩,⟨907,by decide⟩,⟨908,by decide⟩] | 3 => ![⟨284,by decide⟩,⟨909,by decide⟩,⟨910,by decide⟩] | 4 => ![⟨911,by decide⟩,⟨912,by decide⟩,⟨913,by decide⟩] | _ => ![⟨914,by decide⟩,⟨915,by decide⟩,⟨916,by decide⟩]

def ntree7LRRRRL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7LRRRRLL i else ntree7LRRRRLR (i - 5)

def ntree7LRRRRRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨917,by decide⟩,⟨918,by decide⟩,⟨919,by decide⟩] | 1 => ![⟨920,by decide⟩,⟨921,by decide⟩,⟨922,by decide⟩] | 2 => ![⟨923,by decide⟩,⟨924,by decide⟩,⟨925,by decide⟩] | 3 => ![⟨926,by decide⟩,⟨927,by decide⟩,⟨928,by decide⟩] | 4 => ![⟨929,by decide⟩,⟨930,by decide⟩,⟨931,by decide⟩] | _ => ![⟨932,by decide⟩,⟨933,by decide⟩,⟨934,by decide⟩]

def ntree7LRRRRRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨935,by decide⟩,⟨917,by decide⟩,⟨936,by decide⟩] | 1 => ![⟨937,by decide⟩,⟨938,by decide⟩,⟨939,by decide⟩] | 2 => ![⟨914,by decide⟩,⟨940,by decide⟩,⟨941,by decide⟩] | 3 => ![⟨942,by decide⟩,⟨927,by decide⟩,⟨943,by decide⟩] | 4 => ![⟨944,by decide⟩,⟨945,by decide⟩,⟨946,by decide⟩] | _ => ![⟨923,by decide⟩,⟨947,by decide⟩,⟨948,by decide⟩]

def ntree7LRRRRR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7LRRRRRL i else ntree7LRRRRRR (i - 6)

def ntree7LRRRR (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7LRRRRL i else ntree7LRRRRR (i - 11)

def ntree7LRRR (i : Nat) : Fin 3 → Fin 1812 := if i < 23 then ntree7LRRRL i else ntree7LRRRR (i - 23)

def ntree7LRR (i : Nat) : Fin 3 → Fin 1812 := if i < 45 then ntree7LRRL i else ntree7LRRR (i - 45)

def ntree7LR (i : Nat) : Fin 3 → Fin 1812 := if i < 91 then ntree7LRL i else ntree7LRR (i - 91)

def ntree7L (i : Nat) : Fin 3 → Fin 1812 := if i < 182 then ntree7LL i else ntree7LR (i - 182)

def ntree7RLLLLLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨949,by decide⟩,⟨950,by decide⟩,⟨951,by decide⟩] | 1 => ![⟨952,by decide⟩,⟨953,by decide⟩,⟨954,by decide⟩] | 2 => ![⟨932,by decide⟩,⟨955,by decide⟩,⟨956,by decide⟩] | 3 => ![⟨926,by decide⟩,⟨957,by decide⟩,⟨958,by decide⟩] | _ => ![⟨959,by decide⟩,⟨960,by decide⟩,⟨961,by decide⟩]

def ntree7RLLLLLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨962,by decide⟩,⟨963,by decide⟩,⟨941,by decide⟩] | 1 => ![⟨964,by decide⟩,⟨965,by decide⟩,⟨966,by decide⟩] | 2 => ![⟨920,by decide⟩,⟨967,by decide⟩,⟨968,by decide⟩] | 3 => ![⟨969,by decide⟩,⟨970,by decide⟩,⟨948,by decide⟩] | 4 => ![⟨971,by decide⟩,⟨972,by decide⟩,⟨958,by decide⟩] | _ => ![⟨929,by decide⟩,⟨973,by decide⟩,⟨974,by decide⟩]

def ntree7RLLLLL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7RLLLLLL i else ntree7RLLLLLR (i - 5)

def ntree7RLLLLRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨975,by decide⟩,⟨976,by decide⟩,⟨956,by decide⟩] | 1 => ![⟨936,by decide⟩,⟨977,by decide⟩,⟨978,by decide⟩] | 2 => ![⟨937,by decide⟩,⟨979,by decide⟩,⟨980,by decide⟩] | 3 => ![⟨981,by decide⟩,⟨982,by decide⟩,⟨983,by decide⟩] | _ => ![⟨984,by decide⟩,⟨985,by decide⟩,⟨985,by decide⟩]

def ntree7RLLLLRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨986,by decide⟩,⟨987,by decide⟩,⟨919,by decide⟩] | 1 => ![⟨988,by decide⟩,⟨989,by decide⟩,⟨990,by decide⟩] | 2 => ![⟨990,by decide⟩,⟨991,by decide⟩,⟨992,by decide⟩] | 3 => ![⟨993,by decide⟩,⟨994,by decide⟩,⟨928,by decide⟩] | 4 => ![⟨995,by decide⟩,⟨996,by decide⟩,⟨990,by decide⟩] | _ => ![⟨997,by decide⟩,⟨984,by decide⟩,⟨997,by decide⟩]

def ntree7RLLLLR (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7RLLLLRL i else ntree7RLLLLRR (i - 5)

def ntree7RLLLL (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7RLLLLL i else ntree7RLLLLR (i - 11)

def ntree7RLLLRLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨998,by decide⟩,⟨999,by decide⟩,⟨936,by decide⟩] | 1 => ![⟨1000,by decide⟩,⟨1001,by decide⟩,⟨1002,by decide⟩] | 2 => ![⟨1003,by decide⟩,⟨1004,by decide⟩,⟨1005,by decide⟩] | 3 => ![⟨1006,by decide⟩,⟨1007,by decide⟩,⟨943,by decide⟩] | _ => ![⟨1008,by decide⟩,⟨1009,by decide⟩,⟨958,by decide⟩]

def ntree7RLLLRLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1010,by decide⟩,⟨1011,by decide⟩,⟨951,by decide⟩] | 1 => ![⟨1012,by decide⟩,⟨1013,by decide⟩,⟨951,by decide⟩] | 2 => ![⟨1014,by decide⟩,⟨1015,by decide⟩,⟨958,by decide⟩] | 3 => ![⟨1016,by decide⟩,⟨1017,by decide⟩,⟨1018,by decide⟩] | 4 => ![⟨1019,by decide⟩,⟨1020,by decide⟩,⟨958,by decide⟩] | _ => ![⟨1021,by decide⟩,⟨1022,by decide⟩,⟨1023,by decide⟩]

def ntree7RLLLRL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7RLLLRLL i else ntree7RLLLRLR (i - 5)

def ntree7RLLLRRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨984,by decide⟩,⟨984,by decide⟩,⟨1024,by decide⟩] | 1 => ![⟨1025,by decide⟩,⟨1026,by decide⟩,⟨966,by decide⟩] | 2 => ![⟨1027,by decide⟩,⟨1028,by decide⟩,⟨1029,by decide⟩] | 3 => ![⟨990,by decide⟩,⟨1030,by decide⟩,⟨1029,by decide⟩] | 4 => ![⟨1031,by decide⟩,⟨1032,by decide⟩,⟨958,by decide⟩] | _ => ![⟨1033,by decide⟩,⟨1034,by decide⟩,⟨1029,by decide⟩]

def ntree7RLLLRRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨997,by decide⟩,⟨1035,by decide⟩,⟨1036,by decide⟩] | 1 => ![⟨1037,by decide⟩,⟨1038,by decide⟩,⟨978,by decide⟩] | 2 => ![⟨1039,by decide⟩,⟨1040,by decide⟩,⟨1041,by decide⟩] | 3 => ![⟨1042,by decide⟩,⟨1043,by decide⟩,⟨1044,by decide⟩] | 4 => ![⟨1045,by decide⟩,⟨1046,by decide⟩,⟨1047,by decide⟩] | _ => ![⟨1048,by decide⟩,⟨1049,by decide⟩,⟨1050,by decide⟩]

def ntree7RLLLRR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7RLLLRRL i else ntree7RLLLRRR (i - 6)

def ntree7RLLLR (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7RLLLRL i else ntree7RLLLRR (i - 11)

def ntree7RLLL (i : Nat) : Fin 3 → Fin 1812 := if i < 22 then ntree7RLLLL i else ntree7RLLLR (i - 22)

def ntree7RLLRLLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1051,by decide⟩,⟨1052,by decide⟩,⟨1053,by decide⟩] | 1 => ![⟨1054,by decide⟩,⟨1055,by decide⟩,⟨1056,by decide⟩] | 2 => ![⟨1057,by decide⟩,⟨1058,by decide⟩,⟨1059,by decide⟩] | 3 => ![⟨1060,by decide⟩,⟨1061,by decide⟩,⟨1062,by decide⟩] | _ => ![⟨1063,by decide⟩,⟨1064,by decide⟩,⟨1065,by decide⟩]

def ntree7RLLRLLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1066,by decide⟩,⟨1067,by decide⟩,⟨1068,by decide⟩] | 1 => ![⟨1069,by decide⟩,⟨1070,by decide⟩,⟨1071,by decide⟩] | 2 => ![⟨1072,by decide⟩,⟨1073,by decide⟩,⟨1074,by decide⟩] | 3 => ![⟨1075,by decide⟩,⟨1076,by decide⟩,⟨1077,by decide⟩] | 4 => ![⟨1078,by decide⟩,⟨1079,by decide⟩,⟨1080,by decide⟩] | _ => ![⟨1081,by decide⟩,⟨1082,by decide⟩,⟨1083,by decide⟩]

def ntree7RLLRLL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7RLLRLLL i else ntree7RLLRLLR (i - 5)

def ntree7RLLRLRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1084,by decide⟩,⟨1085,by decide⟩,⟨1086,by decide⟩] | 1 => ![⟨1087,by decide⟩,⟨1088,by decide⟩,⟨1089,by decide⟩] | 2 => ![⟨1090,by decide⟩,⟨1091,by decide⟩,⟨1092,by decide⟩] | 3 => ![⟨1093,by decide⟩,⟨1094,by decide⟩,⟨1095,by decide⟩] | 4 => ![⟨1096,by decide⟩,⟨1097,by decide⟩,⟨1098,by decide⟩] | _ => ![⟨1099,by decide⟩,⟨1100,by decide⟩,⟨1101,by decide⟩]

def ntree7RLLRLRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1102,by decide⟩,⟨1103,by decide⟩,⟨1104,by decide⟩] | 1 => ![⟨1105,by decide⟩,⟨1106,by decide⟩,⟨1107,by decide⟩] | 2 => ![⟨1108,by decide⟩,⟨1109,by decide⟩,⟨1110,by decide⟩] | 3 => ![⟨1111,by decide⟩,⟨1112,by decide⟩,⟨1113,by decide⟩] | 4 => ![⟨1114,by decide⟩,⟨1115,by decide⟩,⟨1116,by decide⟩] | _ => ![⟨1117,by decide⟩,⟨1118,by decide⟩,⟨1119,by decide⟩]

def ntree7RLLRLR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7RLLRLRL i else ntree7RLLRLRR (i - 6)

def ntree7RLLRL (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7RLLRLL i else ntree7RLLRLR (i - 11)

def ntree7RLLRRLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1120,by decide⟩,⟨1121,by decide⟩,⟨1122,by decide⟩] | 1 => ![⟨1123,by decide⟩,⟨1124,by decide⟩,⟨1125,by decide⟩] | 2 => ![⟨1126,by decide⟩,⟨1127,by decide⟩,⟨921,by decide⟩] | 3 => ![⟨1128,by decide⟩,⟨1129,by decide⟩,⟨1130,by decide⟩] | _ => ![⟨1131,by decide⟩,⟨1132,by decide⟩,⟨1133,by decide⟩]

def ntree7RLLRRLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1134,by decide⟩,⟨1135,by decide⟩,⟨930,by decide⟩] | 1 => ![⟨1136,by decide⟩,⟨1137,by decide⟩,⟨1138,by decide⟩] | 2 => ![⟨1139,by decide⟩,⟨1140,by decide⟩,⟨1141,by decide⟩] | 3 => ![⟨1126,by decide⟩,⟨1142,by decide⟩,⟨938,by decide⟩] | 4 => ![⟨1143,by decide⟩,⟨1144,by decide⟩,⟨1145,by decide⟩] | _ => ![⟨1146,by decide⟩,⟨1147,by decide⟩,⟨1148,by decide⟩]

def ntree7RLLRRL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7RLLRRLL i else ntree7RLLRRLR (i - 5)

def ntree7RLLRRRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1149,by decide⟩,⟨1150,by decide⟩,⟨945,by decide⟩] | 1 => ![⟨1151,by decide⟩,⟨1152,by decide⟩,⟨1153,by decide⟩] | 2 => ![⟨1154,by decide⟩,⟨1155,by decide⟩,⟨1156,by decide⟩] | 3 => ![⟨1157,by decide⟩,⟨1158,by decide⟩,⟨953,by decide⟩] | 4 => ![⟨1159,by decide⟩,⟨1160,by decide⟩,⟨1161,by decide⟩] | _ => ![⟨1162,by decide⟩,⟨1163,by decide⟩,⟨1164,by decide⟩]

def ntree7RLLRRRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1149,by decide⟩,⟨1165,by decide⟩,⟨960,by decide⟩] | 1 => ![⟨1166,by decide⟩,⟨1144,by decide⟩,⟨1167,by decide⟩] | 2 => ![⟨1168,by decide⟩,⟨1169,by decide⟩,⟨1170,by decide⟩] | 3 => ![⟨1171,by decide⟩,⟨1172,by decide⟩,⟨967,by decide⟩] | 4 => ![⟨1173,by decide⟩,⟨1152,by decide⟩,⟨1174,by decide⟩] | _ => ![⟨1175,by decide⟩,⟨1176,by decide⟩,⟨1177,by decide⟩]

def ntree7RLLRRR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7RLLRRRL i else ntree7RLLRRRR (i - 6)

def ntree7RLLRR (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7RLLRRL i else ntree7RLLRRR (i - 11)

def ntree7RLLR (i : Nat) : Fin 3 → Fin 1812 := if i < 23 then ntree7RLLRL i else ntree7RLLRR (i - 23)

def ntree7RLL (i : Nat) : Fin 3 → Fin 1812 := if i < 45 then ntree7RLLL i else ntree7RLLR (i - 45)

def ntree7RLRLLLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1178,by decide⟩,⟨1179,by decide⟩,⟨973,by decide⟩] | 1 => ![⟨1180,by decide⟩,⟨1160,by decide⟩,⟨1181,by decide⟩] | 2 => ![⟨1182,by decide⟩,⟨1183,by decide⟩,⟨1184,by decide⟩] | 3 => ![⟨1171,by decide⟩,⟨1185,by decide⟩,⟨979,by decide⟩] | _ => ![⟨1186,by decide⟩,⟨1187,by decide⟩,⟨1188,by decide⟩]

def ntree7RLRLLLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1189,by decide⟩,⟨1190,by decide⟩,⟨985,by decide⟩] | 1 => ![⟨1191,by decide⟩,⟨1124,by decide⟩,⟨1192,by decide⟩] | 2 => ![⟨1186,by decide⟩,⟨1193,by decide⟩,⟨1194,by decide⟩] | 3 => ![⟨1195,by decide⟩,⟨1196,by decide⟩,⟨991,by decide⟩] | 4 => ![⟨1197,by decide⟩,⟨1132,by decide⟩,⟨1198,by decide⟩] | _ => ![⟨1199,by decide⟩,⟨1193,by decide⟩,⟨1200,by decide⟩]

def ntree7RLRLLL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7RLRLLLL i else ntree7RLRLLLR (i - 5)

def ntree7RLRLLRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1189,by decide⟩,⟨1201,by decide⟩,⟨984,by decide⟩] | 1 => ![⟨1202,by decide⟩,⟨1140,by decide⟩,⟨1203,by decide⟩] | 2 => ![⟨1204,by decide⟩,⟨1205,by decide⟩,⟨1206,by decide⟩] | 3 => ![⟨1207,by decide⟩,⟨1208,by decide⟩,⟨1004,by decide⟩] | _ => ![⟨1209,by decide⟩,⟨1147,by decide⟩,⟨1198,by decide⟩]

def ntree7RLRLLRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1204,by decide⟩,⟨1210,by decide⟩,⟨1211,by decide⟩] | 1 => ![⟨1212,by decide⟩,⟨1213,by decide⟩,⟨1011,by decide⟩] | 2 => ![⟨1214,by decide⟩,⟨1155,by decide⟩,⟨1215,by decide⟩] | 3 => ![⟨1216,by decide⟩,⟨1210,by decide⟩,⟨1217,by decide⟩] | 4 => ![⟨1207,by decide⟩,⟨1218,by decide⟩,⟨1017,by decide⟩] | _ => ![⟨1219,by decide⟩,⟨1163,by decide⟩,⟨1220,by decide⟩]

def ntree7RLRLLR (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7RLRLLRL i else ntree7RLRLLRR (i - 5)

def ntree7RLRLL (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7RLRLLL i else ntree7RLRLLR (i - 11)

def ntree7RLRLRLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1221,by decide⟩,⟨1222,by decide⟩,⟨1194,by decide⟩] | 1 => ![⟨1223,by decide⟩,⟨1224,by decide⟩,⟨984,by decide⟩] | 2 => ![⟨1225,by decide⟩,⟨1169,by decide⟩,⟨1226,by decide⟩] | 3 => ![⟨1221,by decide⟩,⟨1227,by decide⟩,⟨1228,by decide⟩] | _ => ![⟨1229,by decide⟩,⟨1230,by decide⟩,⟨1030,by decide⟩]

def ntree7RLRLRLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1231,by decide⟩,⟨1176,by decide⟩,⟨1211,by decide⟩] | 1 => ![⟨1232,by decide⟩,⟨1227,by decide⟩,⟨1030,by decide⟩] | 2 => ![⟨1223,by decide⟩,⟨1233,by decide⟩,⟨1035,by decide⟩] | 3 => ![⟨1234,by decide⟩,⟨1183,by decide⟩,⟨977,by decide⟩] | 4 => ![⟨1235,by decide⟩,⟨1236,by decide⟩,⟨1237,by decide⟩] | _ => ![⟨1238,by decide⟩,⟨1239,by decide⟩,⟨1240,by decide⟩]

def ntree7RLRLRL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7RLRLRLL i else ntree7RLRLRLR (i - 5)

def ntree7RLRLRRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1241,by decide⟩,⟨1242,by decide⟩,⟨1243,by decide⟩] | 1 => ![⟨1244,by decide⟩,⟨1245,by decide⟩,⟨1246,by decide⟩] | 2 => ![⟨1247,by decide⟩,⟨1239,by decide⟩,⟨1248,by decide⟩] | 3 => ![⟨1249,by decide⟩,⟨1250,by decide⟩,⟨1251,by decide⟩] | 4 => ![⟨1252,by decide⟩,⟨1236,by decide⟩,⟨1253,by decide⟩] | _ => ![⟨1247,by decide⟩,⟨1254,by decide⟩,⟨1255,by decide⟩]

def ntree7RLRLRRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1256,by decide⟩,⟨1257,by decide⟩,⟨1258,by decide⟩] | 1 => ![⟨1259,by decide⟩,⟨1260,by decide⟩,⟨1261,by decide⟩] | 2 => ![⟨1262,by decide⟩,⟨1263,by decide⟩,⟨1264,by decide⟩] | 3 => ![⟨1265,by decide⟩,⟨1266,by decide⟩,⟨1243,by decide⟩] | 4 => ![⟨1267,by decide⟩,⟨1268,by decide⟩,⟨1269,by decide⟩] | _ => ![⟨1270,by decide⟩,⟨1263,by decide⟩,⟨1271,by decide⟩]

def ntree7RLRLRR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7RLRLRRL i else ntree7RLRLRRR (i - 6)

def ntree7RLRLR (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7RLRLRL i else ntree7RLRLRR (i - 11)

def ntree7RLRL (i : Nat) : Fin 3 → Fin 1812 := if i < 22 then ntree7RLRLL i else ntree7RLRLR (i - 22)

def ntree7RLRRLLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1272,by decide⟩,⟨1273,by decide⟩,⟨1251,by decide⟩] | 1 => ![⟨1274,by decide⟩,⟨1260,by decide⟩,⟨1275,by decide⟩] | 2 => ![⟨1270,by decide⟩,⟨1276,by decide⟩,⟨1277,by decide⟩] | 3 => ![⟨1278,by decide⟩,⟨1279,by decide⟩,⟨1258,by decide⟩] | _ => ![⟨1280,by decide⟩,⟨1281,by decide⟩,⟨1237,by decide⟩]

def ntree7RLRRLLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1282,by decide⟩,⟨1283,by decide⟩,⟨1284,by decide⟩] | 1 => ![⟨1265,by decide⟩,⟨1285,by decide⟩,⟨1286,by decide⟩] | 2 => ![⟨1287,by decide⟩,⟨1288,by decide⟩,⟨1246,by decide⟩] | 3 => ![⟨1289,by decide⟩,⟨1283,by decide⟩,⟨1290,by decide⟩] | 4 => ![⟨1272,by decide⟩,⟨1291,by decide⟩,⟨1292,by decide⟩] | _ => ![⟨1293,by decide⟩,⟨1281,by decide⟩,⟨1253,by decide⟩]

def ntree7RLRRLL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7RLRRLLL i else ntree7RLRRLLR (i - 5)

def ntree7RLRRLRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1289,by decide⟩,⟨1294,by decide⟩,⟨1295,by decide⟩] | 1 => ![⟨1278,by decide⟩,⟨1296,by decide⟩,⟨1297,by decide⟩] | 2 => ![⟨1298,by decide⟩,⟨1299,by decide⟩,⟨1300,by decide⟩] | 3 => ![⟨1301,by decide⟩,⟨1302,by decide⟩,⟨1303,by decide⟩] | 4 => ![⟨1304,by decide⟩,⟨1305,by decide⟩,⟨1306,by decide⟩] | _ => ![⟨1307,by decide⟩,⟨1308,by decide⟩,⟨1309,by decide⟩]

def ntree7RLRRLRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1310,by decide⟩,⟨1311,by decide⟩,⟨1312,by decide⟩] | 1 => ![⟨1313,by decide⟩,⟨1314,by decide⟩,⟨1315,by decide⟩] | 2 => ![⟨1316,by decide⟩,⟨82,by decide⟩,⟨1317,by decide⟩] | 3 => ![⟨1318,by decide⟩,⟨1319,by decide⟩,⟨1320,by decide⟩] | 4 => ![⟨1321,by decide⟩,⟨1322,by decide⟩,⟨1323,by decide⟩] | _ => ![⟨1324,by decide⟩,⟨25,by decide⟩,⟨1325,by decide⟩]

def ntree7RLRRLR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7RLRRLRL i else ntree7RLRRLRR (i - 6)

def ntree7RLRRL (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7RLRRLL i else ntree7RLRRLR (i - 11)

def ntree7RLRRRLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1326,by decide⟩,⟨1327,by decide⟩,⟨1328,by decide⟩] | 1 => ![⟨1329,by decide⟩,⟨1330,by decide⟩,⟨1331,by decide⟩] | 2 => ![⟨1332,by decide⟩,⟨97,by decide⟩,⟨1333,by decide⟩] | 3 => ![⟨1334,by decide⟩,⟨1335,by decide⟩,⟨1336,by decide⟩] | _ => ![⟨1337,by decide⟩,⟨1338,by decide⟩,⟨1339,by decide⟩]

def ntree7RLRRRLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1340,by decide⟩,⟨105,by decide⟩,⟨1341,by decide⟩] | 1 => ![⟨1342,by decide⟩,⟨97,by decide⟩,⟨1343,by decide⟩] | 2 => ![⟨1344,by decide⟩,⟨131,by decide⟩,⟨1345,by decide⟩] | 3 => ![⟨1346,by decide⟩,⟨1347,by decide⟩,⟨1348,by decide⟩] | 4 => ![⟨1349,by decide⟩,⟨1350,by decide⟩,⟨1351,by decide⟩] | _ => ![⟨1352,by decide⟩,⟨1353,by decide⟩,⟨1354,by decide⟩]

def ntree7RLRRRL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7RLRRRLL i else ntree7RLRRRLR (i - 5)

def ntree7RLRRRRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1355,by decide⟩,⟨1356,by decide⟩,⟨1357,by decide⟩] | 1 => ![⟨1358,by decide⟩,⟨1359,by decide⟩,⟨1360,by decide⟩] | 2 => ![⟨1361,by decide⟩,⟨1362,by decide⟩,⟨1363,by decide⟩] | 3 => ![⟨1364,by decide⟩,⟨131,by decide⟩,⟨1365,by decide⟩] | 4 => ![⟨1366,by decide⟩,⟨1367,by decide⟩,⟨1368,by decide⟩] | _ => ![⟨1369,by decide⟩,⟨1370,by decide⟩,⟨1371,by decide⟩]

def ntree7RLRRRRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1372,by decide⟩,⟨1373,by decide⟩,⟨1374,by decide⟩] | 1 => ![⟨1375,by decide⟩,⟨1376,by decide⟩,⟨1377,by decide⟩] | 2 => ![⟨1378,by decide⟩,⟨1379,by decide⟩,⟨1380,by decide⟩] | 3 => ![⟨1381,by decide⟩,⟨1382,by decide⟩,⟨1383,by decide⟩] | 4 => ![⟨1384,by decide⟩,⟨1385,by decide⟩,⟨1386,by decide⟩] | _ => ![⟨1387,by decide⟩,⟨1388,by decide⟩,⟨1389,by decide⟩]

def ntree7RLRRRR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7RLRRRRL i else ntree7RLRRRRR (i - 6)

def ntree7RLRRR (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7RLRRRL i else ntree7RLRRRR (i - 11)

def ntree7RLRR (i : Nat) : Fin 3 → Fin 1812 := if i < 23 then ntree7RLRRL i else ntree7RLRRR (i - 23)

def ntree7RLR (i : Nat) : Fin 3 → Fin 1812 := if i < 45 then ntree7RLRL i else ntree7RLRR (i - 45)

def ntree7RL (i : Nat) : Fin 3 → Fin 1812 := if i < 91 then ntree7RLL i else ntree7RLR (i - 91)

def ntree7RRLLLLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1390,by decide⟩,⟨1391,by decide⟩,⟨1392,by decide⟩] | 1 => ![⟨1393,by decide⟩,⟨1394,by decide⟩,⟨1395,by decide⟩] | 2 => ![⟨1396,by decide⟩,⟨1397,by decide⟩,⟨1398,by decide⟩] | 3 => ![⟨1399,by decide⟩,⟨1400,by decide⟩,⟨1401,by decide⟩] | _ => ![⟨1402,by decide⟩,⟨1403,by decide⟩,⟨1404,by decide⟩]

def ntree7RRLLLLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1405,by decide⟩,⟨1406,by decide⟩,⟨1407,by decide⟩] | 1 => ![⟨1408,by decide⟩,⟨1409,by decide⟩,⟨1410,by decide⟩] | 2 => ![⟨1411,by decide⟩,⟨1412,by decide⟩,⟨1413,by decide⟩] | 3 => ![⟨1414,by decide⟩,⟨1415,by decide⟩,⟨1416,by decide⟩] | 4 => ![⟨1417,by decide⟩,⟨1418,by decide⟩,⟨1419,by decide⟩] | _ => ![⟨1420,by decide⟩,⟨1421,by decide⟩,⟨1422,by decide⟩]

def ntree7RRLLLL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7RRLLLLL i else ntree7RRLLLLR (i - 5)

def ntree7RRLLLRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1423,by decide⟩,⟨1424,by decide⟩,⟨1425,by decide⟩] | 1 => ![⟨1426,by decide⟩,⟨1427,by decide⟩,⟨1428,by decide⟩] | 2 => ![⟨1429,by decide⟩,⟨1430,by decide⟩,⟨1431,by decide⟩] | 3 => ![⟨1432,by decide⟩,⟨1433,by decide⟩,⟨1434,by decide⟩] | _ => ![⟨1435,by decide⟩,⟨1436,by decide⟩,⟨1437,by decide⟩]

def ntree7RRLLLRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1438,by decide⟩,⟨1439,by decide⟩,⟨1440,by decide⟩] | 1 => ![⟨1441,by decide⟩,⟨1442,by decide⟩,⟨1443,by decide⟩] | 2 => ![⟨1444,by decide⟩,⟨1445,by decide⟩,⟨1446,by decide⟩] | 3 => ![⟨1447,by decide⟩,⟨1448,by decide⟩,⟨1449,by decide⟩] | 4 => ![⟨1450,by decide⟩,⟨1451,by decide⟩,⟨1452,by decide⟩] | _ => ![⟨1453,by decide⟩,⟨1454,by decide⟩,⟨1455,by decide⟩]

def ntree7RRLLLR (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7RRLLLRL i else ntree7RRLLLRR (i - 5)

def ntree7RRLLL (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7RRLLLL i else ntree7RRLLLR (i - 11)

def ntree7RRLLRLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1456,by decide⟩,⟨1457,by decide⟩,⟨1458,by decide⟩] | 1 => ![⟨1459,by decide⟩,⟨1460,by decide⟩,⟨1461,by decide⟩] | 2 => ![⟨1462,by decide⟩,⟨1463,by decide⟩,⟨1464,by decide⟩] | 3 => ![⟨1465,by decide⟩,⟨1466,by decide⟩,⟨1467,by decide⟩] | _ => ![⟨1468,by decide⟩,⟨1469,by decide⟩,⟨1470,by decide⟩]

def ntree7RRLLRLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1471,by decide⟩,⟨1472,by decide⟩,⟨1473,by decide⟩] | 1 => ![⟨1474,by decide⟩,⟨1475,by decide⟩,⟨1476,by decide⟩] | 2 => ![⟨1477,by decide⟩,⟨1478,by decide⟩,⟨1479,by decide⟩] | 3 => ![⟨1480,by decide⟩,⟨1481,by decide⟩,⟨1482,by decide⟩] | 4 => ![⟨1483,by decide⟩,⟨1484,by decide⟩,⟨1485,by decide⟩] | _ => ![⟨1486,by decide⟩,⟨1487,by decide⟩,⟨1488,by decide⟩]

def ntree7RRLLRL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7RRLLRLL i else ntree7RRLLRLR (i - 5)

def ntree7RRLLRRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1489,by decide⟩,⟨1490,by decide⟩,⟨1491,by decide⟩] | 1 => ![⟨1492,by decide⟩,⟨1493,by decide⟩,⟨1494,by decide⟩] | 2 => ![⟨1495,by decide⟩,⟨1496,by decide⟩,⟨1497,by decide⟩] | 3 => ![⟨1498,by decide⟩,⟨1499,by decide⟩,⟨1500,by decide⟩] | 4 => ![⟨1501,by decide⟩,⟨1502,by decide⟩,⟨1503,by decide⟩] | _ => ![⟨1504,by decide⟩,⟨1505,by decide⟩,⟨1506,by decide⟩]

def ntree7RRLLRRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1507,by decide⟩,⟨1508,by decide⟩,⟨1509,by decide⟩] | 1 => ![⟨1510,by decide⟩,⟨1511,by decide⟩,⟨1512,by decide⟩] | 2 => ![⟨1513,by decide⟩,⟨1514,by decide⟩,⟨1515,by decide⟩] | 3 => ![⟨1516,by decide⟩,⟨1517,by decide⟩,⟨1518,by decide⟩] | 4 => ![⟨1519,by decide⟩,⟨1520,by decide⟩,⟨1521,by decide⟩] | _ => ![⟨1522,by decide⟩,⟨1523,by decide⟩,⟨1524,by decide⟩]

def ntree7RRLLRR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7RRLLRRL i else ntree7RRLLRRR (i - 6)

def ntree7RRLLR (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7RRLLRL i else ntree7RRLLRR (i - 11)

def ntree7RRLL (i : Nat) : Fin 3 → Fin 1812 := if i < 22 then ntree7RRLLL i else ntree7RRLLR (i - 22)

def ntree7RRLRLLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1525,by decide⟩,⟨1526,by decide⟩,⟨1527,by decide⟩] | 1 => ![⟨1528,by decide⟩,⟨1529,by decide⟩,⟨1530,by decide⟩] | 2 => ![⟨1531,by decide⟩,⟨1532,by decide⟩,⟨1533,by decide⟩] | 3 => ![⟨1534,by decide⟩,⟨1535,by decide⟩,⟨1536,by decide⟩] | _ => ![⟨1537,by decide⟩,⟨918,by decide⟩,⟨1538,by decide⟩]

def ntree7RRLRLLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1539,by decide⟩,⟨1540,by decide⟩,⟨1541,by decide⟩] | 1 => ![⟨1542,by decide⟩,⟨1543,by decide⟩,⟨1544,by decide⟩] | 2 => ![⟨1545,by decide⟩,⟨927,by decide⟩,⟨1546,by decide⟩] | 3 => ![⟨1547,by decide⟩,⟨1548,by decide⟩,⟨1549,by decide⟩] | 4 => ![⟨1550,by decide⟩,⟨1551,by decide⟩,⟨1552,by decide⟩] | _ => ![⟨1553,by decide⟩,⟨917,by decide⟩,⟨1554,by decide⟩]

def ntree7RRLRLL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7RRLRLLL i else ntree7RRLRLLR (i - 5)

def ntree7RRLRLRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1555,by decide⟩,⟨1556,by decide⟩,⟨1557,by decide⟩] | 1 => ![⟨1534,by decide⟩,⟨1551,by decide⟩,⟨1558,by decide⟩] | 2 => ![⟨1559,by decide⟩,⟨927,by decide⟩,⟨1560,by decide⟩] | 3 => ![⟨1561,by decide⟩,⟨1562,by decide⟩,⟨1563,by decide⟩] | 4 => ![⟨1542,by decide⟩,⟨957,by decide⟩,⟨1564,by decide⟩] | _ => ![⟨1565,by decide⟩,⟨950,by decide⟩,⟨1566,by decide⟩]

def ntree7RRLRLRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1567,by decide⟩,⟨1011,by decide⟩,⟨1568,by decide⟩] | 1 => ![⟨1550,by decide⟩,⟨1569,by decide⟩,⟨1570,by decide⟩] | 2 => ![⟨1571,by decide⟩,⟨957,by decide⟩,⟨1572,by decide⟩] | 3 => ![⟨1573,by decide⟩,⟨1574,by decide⟩,⟨1575,by decide⟩] | 4 => ![⟨1576,by decide⟩,⟨1577,by decide⟩,⟨1558,by decide⟩] | _ => ![⟨1578,by decide⟩,⟨965,by decide⟩,⟨1579,by decide⟩]

def ntree7RRLRLR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7RRLRLRL i else ntree7RRLRLRR (i - 6)

def ntree7RRLRL (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7RRLRLL i else ntree7RRLRLR (i - 11)

def ntree7RRLRRLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1539,by decide⟩,⟨1556,by decide⟩,⟨1580,by decide⟩] | 1 => ![⟨1581,by decide⟩,⟨1582,by decide⟩,⟨1564,by decide⟩] | 2 => ![⟨1583,by decide⟩,⟨972,by decide⟩,⟨1584,by decide⟩] | 3 => ![⟨1547,by decide⟩,⟨1585,by decide⟩,⟨1586,by decide⟩] | _ => ![⟨1587,by decide⟩,⟨1574,by decide⟩,⟨1570,by decide⟩]

def ntree7RRLRRLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1588,by decide⟩,⟨977,by decide⟩,⟨1589,by decide⟩] | 1 => ![⟨1555,by decide⟩,⟨1590,by decide⟩,⟨1591,by decide⟩] | 2 => ![⟨1592,by decide⟩,⟨1593,by decide⟩,⟨1594,by decide⟩] | 3 => ![⟨1595,by decide⟩,⟨1596,by decide⟩,⟨1597,by decide⟩] | 4 => ![⟨1598,by decide⟩,⟨987,by decide⟩,⟨1538,by decide⟩] | _ => ![⟨1599,by decide⟩,⟨1600,by decide⟩,⟨1601,by decide⟩]

def ntree7RRLRRL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7RRLRRLL i else ntree7RRLRRLR (i - 5)

def ntree7RRLRRRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1602,by decide⟩,⟨1603,by decide⟩,⟨1604,by decide⟩] | 1 => ![⟨1605,by decide⟩,⟨994,by decide⟩,⟨1546,by decide⟩] | 2 => ![⟨1606,by decide⟩,⟨1607,by decide⟩,⟨1601,by decide⟩] | 3 => ![⟨1608,by decide⟩,⟨1609,by decide⟩,⟨1610,by decide⟩] | 4 => ![⟨1611,by decide⟩,⟨999,by decide⟩,⟨1554,by decide⟩] | _ => ![⟨1612,by decide⟩,⟨1613,by decide⟩,⟨1614,by decide⟩]

def ntree7RRLRRRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1615,by decide⟩,⟨1616,by decide⟩,⟨1617,by decide⟩] | 1 => ![⟨1618,by decide⟩,⟨1007,by decide⟩,⟨1560,by decide⟩] | 2 => ![⟨1619,by decide⟩,⟨1620,by decide⟩,⟨1621,by decide⟩] | 3 => ![⟨1622,by decide⟩,⟨1623,by decide⟩,⟨1624,by decide⟩] | 4 => ![⟨1625,by decide⟩,⟨1013,by decide⟩,⟨1566,by decide⟩] | _ => ![⟨1626,by decide⟩,⟨1627,by decide⟩,⟨1621,by decide⟩]

def ntree7RRLRRR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7RRLRRRL i else ntree7RRLRRRR (i - 6)

def ntree7RRLRR (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7RRLRRL i else ntree7RRLRRR (i - 11)

def ntree7RRLR (i : Nat) : Fin 3 → Fin 1812 := if i < 23 then ntree7RRLRL i else ntree7RRLRR (i - 23)

def ntree7RRL (i : Nat) : Fin 3 → Fin 1812 := if i < 45 then ntree7RRLL i else ntree7RRLR (i - 45)

def ntree7RRRLLLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1628,by decide⟩,⟨1629,by decide⟩,⟨1630,by decide⟩] | 1 => ![⟨1631,by decide⟩,⟨1020,by decide⟩,⟨1572,by decide⟩] | 2 => ![⟨1632,by decide⟩,⟨1633,by decide⟩,⟨1634,by decide⟩] | 3 => ![⟨1595,by decide⟩,⟨1635,by decide⟩,⟨1636,by decide⟩] | _ => ![⟨1637,by decide⟩,⟨1026,by decide⟩,⟨1579,by decide⟩]

def ntree7RRRLLLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1638,by decide⟩,⟨1639,by decide⟩,⟨1640,by decide⟩] | 1 => ![⟨1602,by decide⟩,⟨1641,by decide⟩,⟨1642,by decide⟩] | 2 => ![⟨1643,by decide⟩,⟨1032,by decide⟩,⟨1584,by decide⟩] | 3 => ![⟨1644,by decide⟩,⟨1645,by decide⟩,⟨1640,by decide⟩] | 4 => ![⟨1608,by decide⟩,⟨1646,by decide⟩,⟨1647,by decide⟩] | _ => ![⟨1648,by decide⟩,⟨1038,by decide⟩,⟨1589,by decide⟩]

def ntree7RRRLLL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7RRRLLLL i else ntree7RRRLLLR (i - 5)

def ntree7RRRLLRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1649,by decide⟩,⟨1650,by decide⟩,⟨1651,by decide⟩] | 1 => ![⟨1652,by decide⟩,⟨1653,by decide⟩,⟨1654,by decide⟩] | 2 => ![⟨433,by decide⟩,⟨1655,by decide⟩,⟨1656,by decide⟩] | 3 => ![⟨1657,by decide⟩,⟨1658,by decide⟩,⟨1659,by decide⟩] | 4 => ![⟨1660,by decide⟩,⟨1661,by decide⟩,⟨1662,by decide⟩] | _ => ![⟨1663,by decide⟩,⟨1664,by decide⟩,⟨1665,by decide⟩]

def ntree7RRRLLRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1666,by decide⟩,⟨1667,by decide⟩,⟨1668,by decide⟩] | 1 => ![⟨1669,by decide⟩,⟨1670,by decide⟩,⟨1671,by decide⟩] | 2 => ![⟨1672,by decide⟩,⟨1673,by decide⟩,⟨1674,by decide⟩] | 3 => ![⟨1675,by decide⟩,⟨1676,by decide⟩,⟨1677,by decide⟩] | 4 => ![⟨1678,by decide⟩,⟨1679,by decide⟩,⟨1680,by decide⟩] | _ => ![⟨30,by decide⟩,⟨1330,by decide⟩,⟨1681,by decide⟩]

def ntree7RRRLLR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7RRRLLRL i else ntree7RRRLLRR (i - 6)

def ntree7RRRLL (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7RRRLLL i else ntree7RRRLLR (i - 11)

def ntree7RRRLRLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1682,by decide⟩,⟨1683,by decide⟩,⟨1684,by decide⟩] | 1 => ![⟨1685,by decide⟩,⟨1686,by decide⟩,⟨1687,by decide⟩] | 2 => ![⟨1688,by decide⟩,⟨1689,by decide⟩,⟨1690,by decide⟩] | 3 => ![⟨1691,by decide⟩,⟨1692,by decide⟩,⟨1693,by decide⟩] | _ => ![⟨1694,by decide⟩,⟨1695,by decide⟩,⟨1696,by decide⟩]

def ntree7RRRLRLR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1697,by decide⟩,⟨1698,by decide⟩,⟨1699,by decide⟩] | 1 => ![⟨1700,by decide⟩,⟨1701,by decide⟩,⟨1702,by decide⟩] | 2 => ![⟨1703,by decide⟩,⟨1704,by decide⟩,⟨1705,by decide⟩] | 3 => ![⟨484,by decide⟩,⟨500,by decide⟩,⟨433,by decide⟩] | 4 => ![⟨1706,by decide⟩,⟨1707,by decide⟩,⟨1708,by decide⟩] | _ => ![⟨1709,by decide⟩,⟨1710,by decide⟩,⟨1711,by decide⟩]

def ntree7RRRLRL (i : Nat) : Fin 3 → Fin 1812 := if i < 5 then ntree7RRRLRLL i else ntree7RRRLRLR (i - 5)

def ntree7RRRLRRL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨492,by decide⟩,⟨1712,by decide⟩,⟨1713,by decide⟩] | 1 => ![⟨1714,by decide⟩,⟨1715,by decide⟩,⟨1716,by decide⟩] | 2 => ![⟨1717,by decide⟩,⟨1718,by decide⟩,⟨1719,by decide⟩] | 3 => ![⟨500,by decide⟩,⟨1720,by decide⟩,⟨1721,by decide⟩] | 4 => ![⟨1722,by decide⟩,⟨1723,by decide⟩,⟨1724,by decide⟩] | _ => ![⟨1725,by decide⟩,⟨919,by decide⟩,⟨1125,by decide⟩]

def ntree7RRRLRRR (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1556,by decide⟩,⟨1540,by decide⟩,⟨1540,by decide⟩] | 1 => ![⟨1726,by decide⟩,⟨1727,by decide⟩,⟨1728,by decide⟩] | 2 => ![⟨1729,by decide⟩,⟨1730,by decide⟩,⟨1133,by decide⟩] | 3 => ![⟨1731,by decide⟩,⟨1732,by decide⟩,⟨1548,by decide⟩] | 4 => ![⟨1733,by decide⟩,⟨1734,by decide⟩,⟨1735,by decide⟩] | _ => ![⟨1736,by decide⟩,⟨1737,by decide⟩,⟨1141,by decide⟩]

def ntree7RRRLRR (i : Nat) : Fin 3 → Fin 1812 := if i < 6 then ntree7RRRLRRL i else ntree7RRRLRRR (i - 6)

def ntree7RRRLR (i : Nat) : Fin 3 → Fin 1812 := if i < 11 then ntree7RRRLRL i else ntree7RRRLRR (i - 11)

def ntree7RRRL (i : Nat) : Fin 3 → Fin 1812 := if i < 23 then ntree7RRRLL i else ntree7RRRLR (i - 23)

def ntree7RRRRLLL (i : Nat) : Fin 3 → Fin 1812 := match i with | 0 => ![⟨1556,by decide⟩,⟨1738,by decide⟩,⟨1556,by decide⟩] | 1 => ![⟨1739,by decide⟩,⟨1740,by decide⟩,⟨1741,by decide⟩] | 2 => ![⟨1742,by decide⟩,⟨1743,by decide⟩,⟨1148,by decide⟩] | 3 => ![⟨1740,by decide⟩,⟨1744,by decide⟩,⟨1562,by decide⟩] | _ => ![⟨1745,by decide⟩,⟨1746,by decide⟩,⟨1747,by decide⟩]

end Paper2.Certificates.Q6.Coverage
