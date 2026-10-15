import Paper2.Certificates.Q6CoverageCompact.Layer08Part006

namespace Paper2.Certificates.Q6.Coverage

def stree8LRLLLLRLR (i : Nat) : State := match i with | 0 => state8_861 | 1 => state8_862 | 2 => state8_863 | 3 => state8_864 | 4 => state8_865 | 5 => state8_866 | _ => state8_867

def stree8LRLLLLRL (i : Nat) : State := if i < 6 then stree8LRLLLLRLL i else stree8LRLLLLRLR (i - 6)

def stree8LRLLLLRRL (i : Nat) : State := match i with | 0 => state8_868 | 1 => state8_869 | 2 => state8_870 | 3 => state8_871 | 4 => state8_872 | _ => state8_873

def stree8LRLLLLRRR (i : Nat) : State := match i with | 0 => state8_874 | 1 => state8_875 | 2 => state8_876 | 3 => state8_877 | 4 => state8_878 | 5 => state8_879 | _ => state8_880

def stree8LRLLLLRR (i : Nat) : State := if i < 6 then stree8LRLLLLRRL i else stree8LRLLLLRRR (i - 6)

def stree8LRLLLLR (i : Nat) : State := if i < 13 then stree8LRLLLLRL i else stree8LRLLLLRR (i - 13)

def stree8LRLLLL (i : Nat) : State := if i < 25 then stree8LRLLLLL i else stree8LRLLLLR (i - 25)

def stree8LRLLLRLLL (i : Nat) : State := match i with | 0 => state8_881 | 1 => state8_882 | 2 => state8_883 | 3 => state8_884 | 4 => state8_885 | _ => state8_886

def stree8LRLLLRLLR (i : Nat) : State := match i with | 0 => state8_887 | 1 => state8_888 | 2 => state8_889 | 3 => state8_890 | 4 => state8_891 | 5 => state8_892 | _ => state8_893

def stree8LRLLLRLL (i : Nat) : State := if i < 6 then stree8LRLLLRLLL i else stree8LRLLLRLLR (i - 6)

def stree8LRLLLRLRL (i : Nat) : State := match i with | 0 => state8_894 | 1 => state8_895 | 2 => state8_896 | 3 => state8_897 | 4 => state8_898 | _ => state8_899

def stree8LRLLLRLRR (i : Nat) : State := match i with | 0 => state8_900 | 1 => state8_901 | 2 => state8_902 | 3 => state8_903 | 4 => state8_904 | 5 => state8_905 | _ => state8_906

def stree8LRLLLRLR (i : Nat) : State := if i < 6 then stree8LRLLLRLRL i else stree8LRLLLRLRR (i - 6)

def stree8LRLLLRL (i : Nat) : State := if i < 13 then stree8LRLLLRLL i else stree8LRLLLRLR (i - 13)

def stree8LRLLLRRLL (i : Nat) : State := match i with | 0 => state8_907 | 1 => state8_908 | 2 => state8_909 | 3 => state8_910 | 4 => state8_911 | _ => state8_912

def stree8LRLLLRRLR (i : Nat) : State := match i with | 0 => state8_913 | 1 => state8_914 | 2 => state8_915 | 3 => state8_916 | 4 => state8_917 | 5 => state8_918 | _ => state8_919

def stree8LRLLLRRL (i : Nat) : State := if i < 6 then stree8LRLLLRRLL i else stree8LRLLLRRLR (i - 6)

def stree8LRLLLRRRL (i : Nat) : State := match i with | 0 => state8_920 | 1 => state8_921 | 2 => state8_922 | 3 => state8_923 | 4 => state8_924 | _ => state8_925

def stree8LRLLLRRRR (i : Nat) : State := match i with | 0 => state8_926 | 1 => state8_927 | 2 => state8_928 | 3 => state8_929 | 4 => state8_930 | 5 => state8_931 | _ => state8_932

def stree8LRLLLRRR (i : Nat) : State := if i < 6 then stree8LRLLLRRRL i else stree8LRLLLRRRR (i - 6)

def stree8LRLLLRR (i : Nat) : State := if i < 13 then stree8LRLLLRRL i else stree8LRLLLRRR (i - 13)

def stree8LRLLLR (i : Nat) : State := if i < 26 then stree8LRLLLRL i else stree8LRLLLRR (i - 26)

def stree8LRLLL (i : Nat) : State := if i < 51 then stree8LRLLLL i else stree8LRLLLR (i - 51)

def stree8LRLLRLLLL (i : Nat) : State := match i with | 0 => state8_933 | 1 => state8_934 | 2 => state8_935 | 3 => state8_936 | 4 => state8_937 | _ => state8_938

def stree8LRLLRLLLR (i : Nat) : State := match i with | 0 => state8_939 | 1 => state8_940 | 2 => state8_941 | 3 => state8_942 | 4 => state8_943 | 5 => state8_944 | _ => state8_945

def stree8LRLLRLLL (i : Nat) : State := if i < 6 then stree8LRLLRLLLL i else stree8LRLLRLLLR (i - 6)

def stree8LRLLRLLRL (i : Nat) : State := match i with | 0 => state8_946 | 1 => state8_947 | 2 => state8_948 | 3 => state8_949 | 4 => state8_950 | _ => state8_951

def stree8LRLLRLLRR (i : Nat) : State := match i with | 0 => state8_952 | 1 => state8_953 | 2 => state8_954 | 3 => state8_955 | 4 => state8_956 | 5 => state8_957 | _ => state8_958

def stree8LRLLRLLR (i : Nat) : State := if i < 6 then stree8LRLLRLLRL i else stree8LRLLRLLRR (i - 6)

def stree8LRLLRLL (i : Nat) : State := if i < 13 then stree8LRLLRLLL i else stree8LRLLRLLR (i - 13)

def stree8LRLLRLRLL (i : Nat) : State := match i with | 0 => state8_959 | 1 => state8_960 | 2 => state8_961 | 3 => state8_962 | 4 => state8_963 | _ => state8_964

def stree8LRLLRLRLR (i : Nat) : State := match i with | 0 => state8_965 | 1 => state8_966 | 2 => state8_967 | 3 => state8_968 | 4 => state8_969 | 5 => state8_970 | _ => state8_971

def stree8LRLLRLRL (i : Nat) : State := if i < 6 then stree8LRLLRLRLL i else stree8LRLLRLRLR (i - 6)

def stree8LRLLRLRRL (i : Nat) : State := match i with | 0 => state8_972 | 1 => state8_973 | 2 => state8_974 | 3 => state8_975 | 4 => state8_976 | _ => state8_977

def stree8LRLLRLRRR (i : Nat) : State := match i with | 0 => state8_978 | 1 => state8_979 | 2 => state8_980 | 3 => state8_981 | 4 => state8_982 | 5 => state8_983 | _ => state8_984

def stree8LRLLRLRR (i : Nat) : State := if i < 6 then stree8LRLLRLRRL i else stree8LRLLRLRRR (i - 6)

def stree8LRLLRLR (i : Nat) : State := if i < 13 then stree8LRLLRLRL i else stree8LRLLRLRR (i - 13)

def stree8LRLLRL (i : Nat) : State := if i < 26 then stree8LRLLRLL i else stree8LRLLRLR (i - 26)

def stree8LRLLRRLLL (i : Nat) : State := match i with | 0 => state8_985 | 1 => state8_986 | 2 => state8_987 | 3 => state8_988 | 4 => state8_989 | _ => state8_990

def stree8LRLLRRLLR (i : Nat) : State := match i with | 0 => state8_991 | 1 => state8_992 | 2 => state8_993 | 3 => state8_994 | 4 => state8_995 | 5 => state8_996 | _ => state8_997

def stree8LRLLRRLL (i : Nat) : State := if i < 6 then stree8LRLLRRLLL i else stree8LRLLRRLLR (i - 6)

def stree8LRLLRRLRL (i : Nat) : State := match i with | 0 => state8_998 | 1 => state8_999 | 2 => state8_1000 | 3 => state8_1001 | 4 => state8_1002 | _ => state8_1003

def stree8LRLLRRLRR (i : Nat) : State := match i with | 0 => state8_1004 | 1 => state8_1005 | 2 => state8_1006 | 3 => state8_1007 | 4 => state8_1008 | 5 => state8_1009 | _ => state8_1010

def stree8LRLLRRLR (i : Nat) : State := if i < 6 then stree8LRLLRRLRL i else stree8LRLLRRLRR (i - 6)

def stree8LRLLRRL (i : Nat) : State := if i < 13 then stree8LRLLRRLL i else stree8LRLLRRLR (i - 13)

def stree8LRLLRRRLL (i : Nat) : State := match i with | 0 => state8_1011 | 1 => state8_1012 | 2 => state8_1013 | 3 => state8_1014 | 4 => state8_1015 | _ => state8_1016

def stree8LRLLRRRLR (i : Nat) : State := match i with | 0 => state8_1017 | 1 => state8_1018 | 2 => state8_1019 | 3 => state8_1020 | 4 => state8_1021 | 5 => state8_1022 | _ => state8_1023

def stree8LRLLRRRL (i : Nat) : State := if i < 6 then stree8LRLLRRRLL i else stree8LRLLRRRLR (i - 6)

def stree8LRLLRRRRL (i : Nat) : State := match i with | 0 => state8_1024 | 1 => state8_1025 | 2 => state8_1026 | 3 => state8_1027 | 4 => state8_1028 | _ => state8_1029

def stree8LRLLRRRRR (i : Nat) : State := match i with | 0 => state8_1030 | 1 => state8_1031 | 2 => state8_1032 | 3 => state8_1033 | 4 => state8_1034 | 5 => state8_1035 | _ => state8_1036

def stree8LRLLRRRR (i : Nat) : State := if i < 6 then stree8LRLLRRRRL i else stree8LRLLRRRRR (i - 6)

def stree8LRLLRRR (i : Nat) : State := if i < 13 then stree8LRLLRRRL i else stree8LRLLRRRR (i - 13)

def stree8LRLLRR (i : Nat) : State := if i < 26 then stree8LRLLRRL i else stree8LRLLRRR (i - 26)

def stree8LRLLR (i : Nat) : State := if i < 52 then stree8LRLLRL i else stree8LRLLRR (i - 52)

def stree8LRLL (i : Nat) : State := if i < 103 then stree8LRLLL i else stree8LRLLR (i - 103)

def stree8LRLRLLLLL (i : Nat) : State := match i with | 0 => state8_1037 | 1 => state8_1038 | 2 => state8_1039 | 3 => state8_1040 | 4 => state8_1041 | _ => state8_1042

def stree8LRLRLLLLR (i : Nat) : State := match i with | 0 => state8_1043 | 1 => state8_1044 | 2 => state8_1045 | 3 => state8_1046 | 4 => state8_1047 | 5 => state8_1048 | _ => state8_1049

def stree8LRLRLLLL (i : Nat) : State := if i < 6 then stree8LRLRLLLLL i else stree8LRLRLLLLR (i - 6)

def stree8LRLRLLLRL (i : Nat) : State := match i with | 0 => state8_1050 | 1 => state8_1051 | 2 => state8_1052 | 3 => state8_1053 | 4 => state8_1054 | _ => state8_1055

def stree8LRLRLLLRR (i : Nat) : State := match i with | 0 => state8_1056 | 1 => state8_1057 | 2 => state8_1058 | 3 => state8_1059 | 4 => state8_1060 | 5 => state8_1061 | _ => state8_1062

def stree8LRLRLLLR (i : Nat) : State := if i < 6 then stree8LRLRLLLRL i else stree8LRLRLLLRR (i - 6)

def stree8LRLRLLL (i : Nat) : State := if i < 13 then stree8LRLRLLLL i else stree8LRLRLLLR (i - 13)

def stree8LRLRLLRLL (i : Nat) : State := match i with | 0 => state8_1063 | 1 => state8_1064 | 2 => state8_1065 | 3 => state8_1066 | 4 => state8_1067 | _ => state8_1068

def stree8LRLRLLRLR (i : Nat) : State := match i with | 0 => state8_1069 | 1 => state8_1070 | 2 => state8_1071 | 3 => state8_1072 | 4 => state8_1073 | 5 => state8_1074 | _ => state8_1075

def stree8LRLRLLRL (i : Nat) : State := if i < 6 then stree8LRLRLLRLL i else stree8LRLRLLRLR (i - 6)

def stree8LRLRLLRRL (i : Nat) : State := match i with | 0 => state8_1076 | 1 => state8_1077 | 2 => state8_1078 | 3 => state8_1079 | 4 => state8_1080 | _ => state8_1081

def stree8LRLRLLRRR (i : Nat) : State := match i with | 0 => state8_1082 | 1 => state8_1083 | 2 => state8_1084 | 3 => state8_1085 | 4 => state8_1086 | 5 => state8_1087 | _ => state8_1088

def stree8LRLRLLRR (i : Nat) : State := if i < 6 then stree8LRLRLLRRL i else stree8LRLRLLRRR (i - 6)

def stree8LRLRLLR (i : Nat) : State := if i < 13 then stree8LRLRLLRL i else stree8LRLRLLRR (i - 13)

def stree8LRLRLL (i : Nat) : State := if i < 26 then stree8LRLRLLL i else stree8LRLRLLR (i - 26)

def stree8LRLRLRLLL (i : Nat) : State := match i with | 0 => state8_1089 | 1 => state8_1090 | 2 => state8_1091 | 3 => state8_1092 | 4 => state8_1093 | _ => state8_1094

def stree8LRLRLRLLR (i : Nat) : State := match i with | 0 => state8_1095 | 1 => state8_1096 | 2 => state8_1097 | 3 => state8_1098 | 4 => state8_1099 | 5 => state8_1100 | _ => state8_1101

def stree8LRLRLRLL (i : Nat) : State := if i < 6 then stree8LRLRLRLLL i else stree8LRLRLRLLR (i - 6)

def stree8LRLRLRLRL (i : Nat) : State := match i with | 0 => state8_1102 | 1 => state8_1103 | 2 => state8_1104 | 3 => state8_1105 | 4 => state8_1106 | _ => state8_1107

def stree8LRLRLRLRR (i : Nat) : State := match i with | 0 => state8_1108 | 1 => state8_1109 | 2 => state8_1110 | 3 => state8_1111 | 4 => state8_1112 | 5 => state8_1113 | _ => state8_1114

def stree8LRLRLRLR (i : Nat) : State := if i < 6 then stree8LRLRLRLRL i else stree8LRLRLRLRR (i - 6)

def stree8LRLRLRL (i : Nat) : State := if i < 13 then stree8LRLRLRLL i else stree8LRLRLRLR (i - 13)

def stree8LRLRLRRLL (i : Nat) : State := match i with | 0 => state8_1115 | 1 => state8_1116 | 2 => state8_1117 | 3 => state8_1118 | 4 => state8_1119 | _ => state8_1120

def stree8LRLRLRRLR (i : Nat) : State := match i with | 0 => state8_1121 | 1 => state8_1122 | 2 => state8_1123 | 3 => state8_1124 | 4 => state8_1125 | 5 => state8_1126 | _ => state8_1127

def stree8LRLRLRRL (i : Nat) : State := if i < 6 then stree8LRLRLRRLL i else stree8LRLRLRRLR (i - 6)

def stree8LRLRLRRRL (i : Nat) : State := match i with | 0 => state8_1128 | 1 => state8_1129 | 2 => state8_1130 | 3 => state8_1131 | 4 => state8_1132 | _ => state8_1133

def stree8LRLRLRRRR (i : Nat) : State := match i with | 0 => state8_1134 | 1 => state8_1135 | 2 => state8_1136 | 3 => state8_1137 | 4 => state8_1138 | 5 => state8_1139 | _ => state8_1140

def stree8LRLRLRRR (i : Nat) : State := if i < 6 then stree8LRLRLRRRL i else stree8LRLRLRRRR (i - 6)

def stree8LRLRLRR (i : Nat) : State := if i < 13 then stree8LRLRLRRL i else stree8LRLRLRRR (i - 13)

def stree8LRLRLR (i : Nat) : State := if i < 26 then stree8LRLRLRL i else stree8LRLRLRR (i - 26)

def stree8LRLRL (i : Nat) : State := if i < 52 then stree8LRLRLL i else stree8LRLRLR (i - 52)

def stree8LRLRRLLLL (i : Nat) : State := match i with | 0 => state8_1141 | 1 => state8_1142 | 2 => state8_1143 | 3 => state8_1144 | 4 => state8_1145 | _ => state8_1146

def stree8LRLRRLLLR (i : Nat) : State := match i with | 0 => state8_1147 | 1 => state8_1148 | 2 => state8_1149 | 3 => state8_1150 | 4 => state8_1151 | 5 => state8_1152 | _ => state8_1153

def stree8LRLRRLLL (i : Nat) : State := if i < 6 then stree8LRLRRLLLL i else stree8LRLRRLLLR (i - 6)

def stree8LRLRRLLRL (i : Nat) : State := match i with | 0 => state8_1154 | 1 => state8_1155 | 2 => state8_1156 | 3 => state8_1157 | 4 => state8_1158 | _ => state8_1159

def stree8LRLRRLLRR (i : Nat) : State := match i with | 0 => state8_1160 | 1 => state8_1161 | 2 => state8_1162 | 3 => state8_1163 | 4 => state8_1164 | 5 => state8_1165 | _ => state8_1166

def stree8LRLRRLLR (i : Nat) : State := if i < 6 then stree8LRLRRLLRL i else stree8LRLRRLLRR (i - 6)

def stree8LRLRRLL (i : Nat) : State := if i < 13 then stree8LRLRRLLL i else stree8LRLRRLLR (i - 13)

def stree8LRLRRLRLL (i : Nat) : State := match i with | 0 => state8_1167 | 1 => state8_1168 | 2 => state8_1169 | 3 => state8_1170 | 4 => state8_1171 | _ => state8_1172

def stree8LRLRRLRLR (i : Nat) : State := match i with | 0 => state8_1173 | 1 => state8_1174 | 2 => state8_1175 | 3 => state8_1176 | 4 => state8_1177 | 5 => state8_1178 | _ => state8_1179

def stree8LRLRRLRL (i : Nat) : State := if i < 6 then stree8LRLRRLRLL i else stree8LRLRRLRLR (i - 6)

def stree8LRLRRLRRL (i : Nat) : State := match i with | 0 => state8_1180 | 1 => state8_1181 | 2 => state8_1182 | 3 => state8_1183 | 4 => state8_1184 | _ => state8_1185

def stree8LRLRRLRRR (i : Nat) : State := match i with | 0 => state8_1186 | 1 => state8_1187 | 2 => state8_1188 | 3 => state8_1189 | 4 => state8_1190 | 5 => state8_1191 | _ => state8_1192

def stree8LRLRRLRR (i : Nat) : State := if i < 6 then stree8LRLRRLRRL i else stree8LRLRRLRRR (i - 6)

def stree8LRLRRLR (i : Nat) : State := if i < 13 then stree8LRLRRLRL i else stree8LRLRRLRR (i - 13)

def stree8LRLRRL (i : Nat) : State := if i < 26 then stree8LRLRRLL i else stree8LRLRRLR (i - 26)

def stree8LRLRRRLLL (i : Nat) : State := match i with | 0 => state8_1193 | 1 => state8_1194 | 2 => state8_1195 | 3 => state8_1196 | 4 => state8_1197 | _ => state8_1198

def stree8LRLRRRLLR (i : Nat) : State := match i with | 0 => state8_1199 | 1 => state8_1200 | 2 => state8_1201 | 3 => state8_1202 | 4 => state8_1203 | 5 => state8_1204 | _ => state8_1205

def stree8LRLRRRLL (i : Nat) : State := if i < 6 then stree8LRLRRRLLL i else stree8LRLRRRLLR (i - 6)

def stree8LRLRRRLRL (i : Nat) : State := match i with | 0 => state8_1206 | 1 => state8_1207 | 2 => state8_1208 | 3 => state8_1209 | 4 => state8_1210 | _ => state8_1211

def stree8LRLRRRLRR (i : Nat) : State := match i with | 0 => state8_1212 | 1 => state8_1213 | 2 => state8_1214 | 3 => state8_1215 | 4 => state8_1216 | 5 => state8_1217 | _ => state8_1218

def stree8LRLRRRLR (i : Nat) : State := if i < 6 then stree8LRLRRRLRL i else stree8LRLRRRLRR (i - 6)

def stree8LRLRRRL (i : Nat) : State := if i < 13 then stree8LRLRRRLL i else stree8LRLRRRLR (i - 13)

def stree8LRLRRRRLL (i : Nat) : State := match i with | 0 => state8_1219 | 1 => state8_1220 | 2 => state8_1221 | 3 => state8_1222 | 4 => state8_1223 | _ => state8_1224

def stree8LRLRRRRLR (i : Nat) : State := match i with | 0 => state8_1225 | 1 => state8_1226 | 2 => state8_1227 | 3 => state8_1228 | 4 => state8_1229 | 5 => state8_1230 | _ => state8_1231

def stree8LRLRRRRL (i : Nat) : State := if i < 6 then stree8LRLRRRRLL i else stree8LRLRRRRLR (i - 6)

def stree8LRLRRRRRL (i : Nat) : State := match i with | 0 => state8_1232 | 1 => state8_1233 | 2 => state8_1234 | 3 => state8_1235 | 4 => state8_1236 | _ => state8_1237

def stree8LRLRRRRRR (i : Nat) : State := match i with | 0 => state8_1238 | 1 => state8_1239 | 2 => state8_1240 | 3 => state8_1241 | 4 => state8_1242 | 5 => state8_1243 | _ => state8_1244

def stree8LRLRRRRR (i : Nat) : State := if i < 6 then stree8LRLRRRRRL i else stree8LRLRRRRRR (i - 6)

def stree8LRLRRRR (i : Nat) : State := if i < 13 then stree8LRLRRRRL i else stree8LRLRRRRR (i - 13)

def stree8LRLRRR (i : Nat) : State := if i < 26 then stree8LRLRRRL i else stree8LRLRRRR (i - 26)

def stree8LRLRR (i : Nat) : State := if i < 52 then stree8LRLRRL i else stree8LRLRRR (i - 52)

def stree8LRLR (i : Nat) : State := if i < 104 then stree8LRLRL i else stree8LRLRR (i - 104)

def stree8LRL (i : Nat) : State := if i < 207 then stree8LRLL i else stree8LRLR (i - 207)

def stree8LRRLLLLLL (i : Nat) : State := match i with | 0 => state8_1245 | 1 => state8_1246 | 2 => state8_1247 | 3 => state8_1248 | 4 => state8_1249 | _ => state8_1250

def stree8LRRLLLLLR (i : Nat) : State := match i with | 0 => state8_1251 | 1 => state8_1252 | 2 => state8_1253 | 3 => state8_1254 | 4 => state8_1255 | _ => state8_1256

def stree8LRRLLLLL (i : Nat) : State := if i < 6 then stree8LRRLLLLLL i else stree8LRRLLLLLR (i - 6)

def stree8LRRLLLLRL (i : Nat) : State := match i with | 0 => state8_1257 | 1 => state8_1258 | 2 => state8_1259 | 3 => state8_1260 | 4 => state8_1261 | _ => state8_1262

def stree8LRRLLLLRR (i : Nat) : State := match i with | 0 => state8_1263 | 1 => state8_1264 | 2 => state8_1265 | 3 => state8_1266 | 4 => state8_1267 | 5 => state8_1268 | _ => state8_1269

def stree8LRRLLLLR (i : Nat) : State := if i < 6 then stree8LRRLLLLRL i else stree8LRRLLLLRR (i - 6)

def stree8LRRLLLL (i : Nat) : State := if i < 12 then stree8LRRLLLLL i else stree8LRRLLLLR (i - 12)

def stree8LRRLLLRLL (i : Nat) : State := match i with | 0 => state8_1270 | 1 => state8_1271 | 2 => state8_1272 | 3 => state8_1273 | 4 => state8_1274 | _ => state8_1275

def stree8LRRLLLRLR (i : Nat) : State := match i with | 0 => state8_1276 | 1 => state8_1277 | 2 => state8_1278 | 3 => state8_1279 | 4 => state8_1280 | 5 => state8_1281 | _ => state8_1282

def stree8LRRLLLRL (i : Nat) : State := if i < 6 then stree8LRRLLLRLL i else stree8LRRLLLRLR (i - 6)

def stree8LRRLLLRRL (i : Nat) : State := match i with | 0 => state8_1283 | 1 => state8_1284 | 2 => state8_1285 | 3 => state8_1286 | 4 => state8_1287 | _ => state8_1288

def stree8LRRLLLRRR (i : Nat) : State := match i with | 0 => state8_1289 | 1 => state8_1290 | 2 => state8_1291 | 3 => state8_1292 | 4 => state8_1293 | 5 => state8_1294 | _ => state8_1295

def stree8LRRLLLRR (i : Nat) : State := if i < 6 then stree8LRRLLLRRL i else stree8LRRLLLRRR (i - 6)

def stree8LRRLLLR (i : Nat) : State := if i < 13 then stree8LRRLLLRL i else stree8LRRLLLRR (i - 13)

def stree8LRRLLL (i : Nat) : State := if i < 25 then stree8LRRLLLL i else stree8LRRLLLR (i - 25)

def stree8LRRLLRLLL (i : Nat) : State := match i with | 0 => state8_1296 | 1 => state8_1297 | 2 => state8_1298 | 3 => state8_1299 | 4 => state8_1300 | _ => state8_1301

def stree8LRRLLRLLR (i : Nat) : State := match i with | 0 => state8_1302 | 1 => state8_1303 | 2 => state8_1304 | 3 => state8_1305 | 4 => state8_1306 | 5 => state8_1307 | _ => state8_1308

def stree8LRRLLRLL (i : Nat) : State := if i < 6 then stree8LRRLLRLLL i else stree8LRRLLRLLR (i - 6)

def stree8LRRLLRLRL (i : Nat) : State := match i with | 0 => state8_1309 | 1 => state8_1310 | 2 => state8_1311 | 3 => state8_1312 | 4 => state8_1313 | _ => state8_1314

def stree8LRRLLRLRR (i : Nat) : State := match i with | 0 => state8_1315 | 1 => state8_1316 | 2 => state8_1317 | 3 => state8_1318 | 4 => state8_1319 | 5 => state8_1320 | _ => state8_1321

def stree8LRRLLRLR (i : Nat) : State := if i < 6 then stree8LRRLLRLRL i else stree8LRRLLRLRR (i - 6)

def stree8LRRLLRL (i : Nat) : State := if i < 13 then stree8LRRLLRLL i else stree8LRRLLRLR (i - 13)

def stree8LRRLLRRLL (i : Nat) : State := match i with | 0 => state8_1322 | 1 => state8_1323 | 2 => state8_1324 | 3 => state8_1325 | 4 => state8_1326 | _ => state8_1327

def stree8LRRLLRRLR (i : Nat) : State := match i with | 0 => state8_1328 | 1 => state8_1329 | 2 => state8_1330 | 3 => state8_1331 | 4 => state8_1332 | 5 => state8_1333 | _ => state8_1334

def stree8LRRLLRRL (i : Nat) : State := if i < 6 then stree8LRRLLRRLL i else stree8LRRLLRRLR (i - 6)

def stree8LRRLLRRRL (i : Nat) : State := match i with | 0 => state8_1335 | 1 => state8_1336 | 2 => state8_1337 | 3 => state8_1338 | 4 => state8_1339 | _ => state8_1340

def stree8LRRLLRRRR (i : Nat) : State := match i with | 0 => state8_1341 | 1 => state8_1342 | 2 => state8_1343 | 3 => state8_1344 | 4 => state8_1345 | 5 => state8_1346 | _ => state8_1347

def stree8LRRLLRRR (i : Nat) : State := if i < 6 then stree8LRRLLRRRL i else stree8LRRLLRRRR (i - 6)

def stree8LRRLLRR (i : Nat) : State := if i < 13 then stree8LRRLLRRL i else stree8LRRLLRRR (i - 13)

def stree8LRRLLR (i : Nat) : State := if i < 26 then stree8LRRLLRL i else stree8LRRLLRR (i - 26)

def stree8LRRLL (i : Nat) : State := if i < 51 then stree8LRRLLL i else stree8LRRLLR (i - 51)

def stree8LRRLRLLLL (i : Nat) : State := match i with | 0 => state8_1348 | 1 => state8_1349 | 2 => state8_1350 | 3 => state8_1351 | 4 => state8_1352 | _ => state8_1353

def stree8LRRLRLLLR (i : Nat) : State := match i with | 0 => state8_1354 | 1 => state8_1355 | 2 => state8_1356 | 3 => state8_1357 | 4 => state8_1358 | 5 => state8_1359 | _ => state8_1360

def stree8LRRLRLLL (i : Nat) : State := if i < 6 then stree8LRRLRLLLL i else stree8LRRLRLLLR (i - 6)

def stree8LRRLRLLRL (i : Nat) : State := match i with | 0 => state8_1361 | 1 => state8_1362 | 2 => state8_1363 | 3 => state8_1364 | 4 => state8_1365 | _ => state8_1366

def stree8LRRLRLLRR (i : Nat) : State := match i with | 0 => state8_1367 | 1 => state8_1368 | 2 => state8_1369 | 3 => state8_1370 | 4 => state8_1371 | 5 => state8_1372 | _ => state8_1373

def stree8LRRLRLLR (i : Nat) : State := if i < 6 then stree8LRRLRLLRL i else stree8LRRLRLLRR (i - 6)

def stree8LRRLRLL (i : Nat) : State := if i < 13 then stree8LRRLRLLL i else stree8LRRLRLLR (i - 13)

def stree8LRRLRLRLL (i : Nat) : State := match i with | 0 => state8_1374 | 1 => state8_1375 | 2 => state8_1376 | 3 => state8_1377 | 4 => state8_1378 | _ => state8_1379

def stree8LRRLRLRLR (i : Nat) : State := match i with | 0 => state8_1380 | 1 => state8_1381 | 2 => state8_1382 | 3 => state8_1383 | 4 => state8_1384 | 5 => state8_1385 | _ => state8_1386

def stree8LRRLRLRL (i : Nat) : State := if i < 6 then stree8LRRLRLRLL i else stree8LRRLRLRLR (i - 6)

def stree8LRRLRLRRL (i : Nat) : State := match i with | 0 => state8_1387 | 1 => state8_1388 | 2 => state8_1389 | 3 => state8_1390 | 4 => state8_1391 | _ => state8_1392

def stree8LRRLRLRRR (i : Nat) : State := match i with | 0 => state8_1393 | 1 => state8_1394 | 2 => state8_1395 | 3 => state8_1396 | 4 => state8_1397 | 5 => state8_1398 | _ => state8_1399

def stree8LRRLRLRR (i : Nat) : State := if i < 6 then stree8LRRLRLRRL i else stree8LRRLRLRRR (i - 6)

def stree8LRRLRLR (i : Nat) : State := if i < 13 then stree8LRRLRLRL i else stree8LRRLRLRR (i - 13)

def stree8LRRLRL (i : Nat) : State := if i < 26 then stree8LRRLRLL i else stree8LRRLRLR (i - 26)

def stree8LRRLRRLLL (i : Nat) : State := match i with | 0 => state8_1400 | 1 => state8_1401 | 2 => state8_1402 | 3 => state8_1403 | 4 => state8_1404 | _ => state8_1405

def stree8LRRLRRLLR (i : Nat) : State := match i with | 0 => state8_1406 | 1 => state8_1407 | 2 => state8_1408 | 3 => state8_1409 | 4 => state8_1410 | 5 => state8_1411 | _ => state8_1412

def stree8LRRLRRLL (i : Nat) : State := if i < 6 then stree8LRRLRRLLL i else stree8LRRLRRLLR (i - 6)

def stree8LRRLRRLRL (i : Nat) : State := match i with | 0 => state8_1413 | 1 => state8_1414 | 2 => state8_1415 | 3 => state8_1416 | 4 => state8_1417 | _ => state8_1418

def stree8LRRLRRLRR (i : Nat) : State := match i with | 0 => state8_1419 | 1 => state8_1420 | 2 => state8_1421 | 3 => state8_1422 | 4 => state8_1423 | 5 => state8_1424 | _ => state8_1425

def stree8LRRLRRLR (i : Nat) : State := if i < 6 then stree8LRRLRRLRL i else stree8LRRLRRLRR (i - 6)

def stree8LRRLRRL (i : Nat) : State := if i < 13 then stree8LRRLRRLL i else stree8LRRLRRLR (i - 13)

def stree8LRRLRRRLL (i : Nat) : State := match i with | 0 => state8_1426 | 1 => state8_1427 | 2 => state8_1428 | 3 => state8_1429 | 4 => state8_1430 | _ => state8_1431

def stree8LRRLRRRLR (i : Nat) : State := match i with | 0 => state8_1432 | 1 => state8_1433 | 2 => state8_1434 | 3 => state8_1435 | 4 => state8_1436 | 5 => state8_1437 | _ => state8_1438

def stree8LRRLRRRL (i : Nat) : State := if i < 6 then stree8LRRLRRRLL i else stree8LRRLRRRLR (i - 6)

def stree8LRRLRRRRL (i : Nat) : State := match i with | 0 => state8_1439 | 1 => state8_1440 | 2 => state8_1441 | 3 => state8_1442 | 4 => state8_1443 | _ => state8_1444

def stree8LRRLRRRRR (i : Nat) : State := match i with | 0 => state8_1445 | 1 => state8_1446 | 2 => state8_1447 | 3 => state8_1448 | 4 => state8_1449 | 5 => state8_1450 | _ => state8_1451

def stree8LRRLRRRR (i : Nat) : State := if i < 6 then stree8LRRLRRRRL i else stree8LRRLRRRRR (i - 6)

def stree8LRRLRRR (i : Nat) : State := if i < 13 then stree8LRRLRRRL i else stree8LRRLRRRR (i - 13)

def stree8LRRLRR (i : Nat) : State := if i < 26 then stree8LRRLRRL i else stree8LRRLRRR (i - 26)

def stree8LRRLR (i : Nat) : State := if i < 52 then stree8LRRLRL i else stree8LRRLRR (i - 52)

def stree8LRRL (i : Nat) : State := if i < 103 then stree8LRRLL i else stree8LRRLR (i - 103)

def stree8LRRRLLLLL (i : Nat) : State := match i with | 0 => state8_1452 | 1 => state8_1453 | 2 => state8_1454 | 3 => state8_1455 | 4 => state8_1456 | _ => state8_1457

def stree8LRRRLLLLR (i : Nat) : State := match i with | 0 => state8_1458 | 1 => state8_1459 | 2 => state8_1460 | 3 => state8_1461 | 4 => state8_1462 | 5 => state8_1463 | _ => state8_1464

def stree8LRRRLLLL (i : Nat) : State := if i < 6 then stree8LRRRLLLLL i else stree8LRRRLLLLR (i - 6)

def stree8LRRRLLLRL (i : Nat) : State := match i with | 0 => state8_1465 | 1 => state8_1466 | 2 => state8_1467 | 3 => state8_1468 | 4 => state8_1469 | _ => state8_1470

def stree8LRRRLLLRR (i : Nat) : State := match i with | 0 => state8_1471 | 1 => state8_1472 | 2 => state8_1473 | 3 => state8_1474 | 4 => state8_1475 | 5 => state8_1476 | _ => state8_1477

def stree8LRRRLLLR (i : Nat) : State := if i < 6 then stree8LRRRLLLRL i else stree8LRRRLLLRR (i - 6)

def stree8LRRRLLL (i : Nat) : State := if i < 13 then stree8LRRRLLLL i else stree8LRRRLLLR (i - 13)

def stree8LRRRLLRLL (i : Nat) : State := match i with | 0 => state8_1478 | 1 => state8_1479 | 2 => state8_1480 | 3 => state8_1481 | 4 => state8_1482 | _ => state8_1483

def stree8LRRRLLRLR (i : Nat) : State := match i with | 0 => state8_1484 | 1 => state8_1485 | 2 => state8_1486 | 3 => state8_1487 | 4 => state8_1488 | 5 => state8_1489 | _ => state8_1490

def stree8LRRRLLRL (i : Nat) : State := if i < 6 then stree8LRRRLLRLL i else stree8LRRRLLRLR (i - 6)

def stree8LRRRLLRRL (i : Nat) : State := match i with | 0 => state8_1491 | 1 => state8_1492 | 2 => state8_1493 | 3 => state8_1494 | 4 => state8_1495 | _ => state8_1496

def stree8LRRRLLRRR (i : Nat) : State := match i with | 0 => state8_1497 | 1 => state8_1498 | 2 => state8_1499 | 3 => state8_1500 | 4 => state8_1501 | 5 => state8_1502 | _ => state8_1503

def stree8LRRRLLRR (i : Nat) : State := if i < 6 then stree8LRRRLLRRL i else stree8LRRRLLRRR (i - 6)

def stree8LRRRLLR (i : Nat) : State := if i < 13 then stree8LRRRLLRL i else stree8LRRRLLRR (i - 13)

def stree8LRRRLL (i : Nat) : State := if i < 26 then stree8LRRRLLL i else stree8LRRRLLR (i - 26)

def stree8LRRRLRLLL (i : Nat) : State := match i with | 0 => state8_1504 | 1 => state8_1505 | 2 => state8_1506 | 3 => state8_1507 | 4 => state8_1508 | _ => state8_1509

def stree8LRRRLRLLR (i : Nat) : State := match i with | 0 => state8_1510 | 1 => state8_1511 | 2 => state8_1512 | 3 => state8_1513 | 4 => state8_1514 | 5 => state8_1515 | _ => state8_1516

def stree8LRRRLRLL (i : Nat) : State := if i < 6 then stree8LRRRLRLLL i else stree8LRRRLRLLR (i - 6)

def stree8LRRRLRLRL (i : Nat) : State := match i with | 0 => state8_1517 | 1 => state8_1518 | 2 => state8_1519 | 3 => state8_1520 | 4 => state8_1521 | _ => state8_1522

def stree8LRRRLRLRR (i : Nat) : State := match i with | 0 => state8_1523 | 1 => state8_1524 | 2 => state8_1525 | 3 => state8_1526 | 4 => state8_1527 | 5 => state8_1528 | _ => state8_1529

def stree8LRRRLRLR (i : Nat) : State := if i < 6 then stree8LRRRLRLRL i else stree8LRRRLRLRR (i - 6)

def stree8LRRRLRL (i : Nat) : State := if i < 13 then stree8LRRRLRLL i else stree8LRRRLRLR (i - 13)

def stree8LRRRLRRLL (i : Nat) : State := match i with | 0 => state8_1530 | 1 => state8_1531 | 2 => state8_1532 | 3 => state8_1533 | 4 => state8_1534 | _ => state8_1535

def stree8LRRRLRRLR (i : Nat) : State := match i with | 0 => state8_1536 | 1 => state8_1537 | 2 => state8_1538 | 3 => state8_1539 | 4 => state8_1540 | 5 => state8_1541 | _ => state8_1542

def stree8LRRRLRRL (i : Nat) : State := if i < 6 then stree8LRRRLRRLL i else stree8LRRRLRRLR (i - 6)

def stree8LRRRLRRRL (i : Nat) : State := match i with | 0 => state8_1543 | 1 => state8_1544 | 2 => state8_1545 | 3 => state8_1546 | 4 => state8_1547 | _ => state8_1548

def stree8LRRRLRRRR (i : Nat) : State := match i with | 0 => state8_1549 | 1 => state8_1550 | 2 => state8_1551 | 3 => state8_1552 | 4 => state8_1553 | 5 => state8_1554 | _ => state8_1555

def stree8LRRRLRRR (i : Nat) : State := if i < 6 then stree8LRRRLRRRL i else stree8LRRRLRRRR (i - 6)

def stree8LRRRLRR (i : Nat) : State := if i < 13 then stree8LRRRLRRL i else stree8LRRRLRRR (i - 13)

def stree8LRRRLR (i : Nat) : State := if i < 26 then stree8LRRRLRL i else stree8LRRRLRR (i - 26)

def stree8LRRRL (i : Nat) : State := if i < 52 then stree8LRRRLL i else stree8LRRRLR (i - 52)

def stree8LRRRRLLLL (i : Nat) : State := match i with | 0 => state8_1556 | 1 => state8_1557 | 2 => state8_1558 | 3 => state8_1559 | 4 => state8_1560 | _ => state8_1561

def stree8LRRRRLLLR (i : Nat) : State := match i with | 0 => state8_1562 | 1 => state8_1563 | 2 => state8_1564 | 3 => state8_1565 | 4 => state8_1566 | 5 => state8_1567 | _ => state8_1568

def stree8LRRRRLLL (i : Nat) : State := if i < 6 then stree8LRRRRLLLL i else stree8LRRRRLLLR (i - 6)

def stree8LRRRRLLRL (i : Nat) : State := match i with | 0 => state8_1569 | 1 => state8_1570 | 2 => state8_1571 | 3 => state8_1572 | 4 => state8_1573 | _ => state8_1574

def stree8LRRRRLLRR (i : Nat) : State := match i with | 0 => state8_1575 | 1 => state8_1576 | 2 => state8_1577 | 3 => state8_1578 | 4 => state8_1579 | 5 => state8_1580 | _ => state8_1581

def stree8LRRRRLLR (i : Nat) : State := if i < 6 then stree8LRRRRLLRL i else stree8LRRRRLLRR (i - 6)

def stree8LRRRRLL (i : Nat) : State := if i < 13 then stree8LRRRRLLL i else stree8LRRRRLLR (i - 13)

def stree8LRRRRLRLL (i : Nat) : State := match i with | 0 => state8_1582 | 1 => state8_1583 | 2 => state8_1584 | 3 => state8_1585 | 4 => state8_1586 | _ => state8_1587

def stree8LRRRRLRLR (i : Nat) : State := match i with | 0 => state8_1588 | 1 => state8_1589 | 2 => state8_1590 | 3 => state8_1591 | 4 => state8_1592 | 5 => state8_1593 | _ => state8_1594

def stree8LRRRRLRL (i : Nat) : State := if i < 6 then stree8LRRRRLRLL i else stree8LRRRRLRLR (i - 6)

def stree8LRRRRLRRL (i : Nat) : State := match i with | 0 => state8_1595 | 1 => state8_1596 | 2 => state8_1597 | 3 => state8_1598 | 4 => state8_1599 | _ => state8_1600

def stree8LRRRRLRRR (i : Nat) : State := match i with | 0 => state8_1601 | 1 => state8_1602 | 2 => state8_1603 | 3 => state8_1604 | 4 => state8_1605 | 5 => state8_1606 | _ => state8_1607

def stree8LRRRRLRR (i : Nat) : State := if i < 6 then stree8LRRRRLRRL i else stree8LRRRRLRRR (i - 6)

def stree8LRRRRLR (i : Nat) : State := if i < 13 then stree8LRRRRLRL i else stree8LRRRRLRR (i - 13)

def stree8LRRRRL (i : Nat) : State := if i < 26 then stree8LRRRRLL i else stree8LRRRRLR (i - 26)

def stree8LRRRRRLLL (i : Nat) : State := match i with | 0 => state8_1608 | 1 => state8_1609 | 2 => state8_1610 | 3 => state8_1611 | 4 => state8_1612 | _ => state8_1613

def stree8LRRRRRLLR (i : Nat) : State := match i with | 0 => state8_1614 | 1 => state8_1615 | 2 => state8_1616 | 3 => state8_1617 | 4 => state8_1618 | 5 => state8_1619 | _ => state8_1620

def stree8LRRRRRLL (i : Nat) : State := if i < 6 then stree8LRRRRRLLL i else stree8LRRRRRLLR (i - 6)

def stree8LRRRRRLRL (i : Nat) : State := match i with | 0 => state8_1621 | 1 => state8_1622 | 2 => state8_1623 | 3 => state8_1624 | 4 => state8_1625 | _ => state8_1626

def stree8LRRRRRLRR (i : Nat) : State := match i with | 0 => state8_1627 | 1 => state8_1628 | 2 => state8_1629 | 3 => state8_1630 | 4 => state8_1631 | 5 => state8_1632 | _ => state8_1633

def stree8LRRRRRLR (i : Nat) : State := if i < 6 then stree8LRRRRRLRL i else stree8LRRRRRLRR (i - 6)

def stree8LRRRRRL (i : Nat) : State := if i < 13 then stree8LRRRRRLL i else stree8LRRRRRLR (i - 13)

def stree8LRRRRRRLL (i : Nat) : State := match i with | 0 => state8_1634 | 1 => state8_1635 | 2 => state8_1636 | 3 => state8_1637 | 4 => state8_1638 | _ => state8_1639

def stree8LRRRRRRLR (i : Nat) : State := match i with | 0 => state8_1640 | 1 => state8_1641 | 2 => state8_1642 | 3 => state8_1643 | 4 => state8_1644 | 5 => state8_1645 | _ => state8_1646

def stree8LRRRRRRL (i : Nat) : State := if i < 6 then stree8LRRRRRRLL i else stree8LRRRRRRLR (i - 6)

def stree8LRRRRRRRL (i : Nat) : State := match i with | 0 => state8_1647 | 1 => state8_1648 | 2 => state8_1649 | 3 => state8_1650 | 4 => state8_1651 | _ => state8_1652

def stree8LRRRRRRRR (i : Nat) : State := match i with | 0 => state8_1653 | 1 => state8_1654 | 2 => state8_1655 | 3 => state8_1656 | 4 => state8_1657 | 5 => state8_1658 | _ => state8_1659

def stree8LRRRRRRR (i : Nat) : State := if i < 6 then stree8LRRRRRRRL i else stree8LRRRRRRRR (i - 6)

def stree8LRRRRRR (i : Nat) : State := if i < 13 then stree8LRRRRRRL i else stree8LRRRRRRR (i - 13)

def stree8LRRRRR (i : Nat) : State := if i < 26 then stree8LRRRRRL i else stree8LRRRRRR (i - 26)

def stree8LRRRR (i : Nat) : State := if i < 52 then stree8LRRRRL i else stree8LRRRRR (i - 52)

def stree8LRRR (i : Nat) : State := if i < 104 then stree8LRRRL i else stree8LRRRR (i - 104)

def stree8LRR (i : Nat) : State := if i < 207 then stree8LRRL i else stree8LRRR (i - 207)

def stree8LR (i : Nat) : State := if i < 415 then stree8LRL i else stree8LRR (i - 415)

def stree8L (i : Nat) : State := if i < 830 then stree8LL i else stree8LR (i - 830)

def stree8RLLLLLLLL (i : Nat) : State := match i with | 0 => state8_1660 | 1 => state8_1661 | 2 => state8_1662 | 3 => state8_1663 | 4 => state8_1664 | _ => state8_1665

def stree8RLLLLLLLR (i : Nat) : State := match i with | 0 => state8_1666 | 1 => state8_1667 | 2 => state8_1668 | 3 => state8_1669 | 4 => state8_1670 | _ => state8_1671

def stree8RLLLLLLL (i : Nat) : State := if i < 6 then stree8RLLLLLLLL i else stree8RLLLLLLLR (i - 6)

def stree8RLLLLLLRL (i : Nat) : State := match i with | 0 => state8_1672 | 1 => state8_1673 | 2 => state8_1674 | 3 => state8_1675 | 4 => state8_1676 | _ => state8_1677

def stree8RLLLLLLRR (i : Nat) : State := match i with | 0 => state8_1678 | 1 => state8_1679 | 2 => state8_1680 | 3 => state8_1681 | 4 => state8_1682 | 5 => state8_1683 | _ => state8_1684

def stree8RLLLLLLR (i : Nat) : State := if i < 6 then stree8RLLLLLLRL i else stree8RLLLLLLRR (i - 6)

def stree8RLLLLLL (i : Nat) : State := if i < 12 then stree8RLLLLLLL i else stree8RLLLLLLR (i - 12)

def stree8RLLLLLRLL (i : Nat) : State := match i with | 0 => state8_1685 | 1 => state8_1686 | 2 => state8_1687 | 3 => state8_1688 | 4 => state8_1689 | _ => state8_1690

def stree8RLLLLLRLR (i : Nat) : State := match i with | 0 => state8_1691 | 1 => state8_1692 | 2 => state8_1693 | 3 => state8_1694 | 4 => state8_1695 | 5 => state8_1696 | _ => state8_1697

def stree8RLLLLLRL (i : Nat) : State := if i < 6 then stree8RLLLLLRLL i else stree8RLLLLLRLR (i - 6)

def stree8RLLLLLRRL (i : Nat) : State := match i with | 0 => state8_1698 | 1 => state8_1699 | 2 => state8_1700 | 3 => state8_1701 | 4 => state8_1702 | _ => state8_1703

def stree8RLLLLLRRR (i : Nat) : State := match i with | 0 => state8_1704 | 1 => state8_1705 | 2 => state8_1706 | 3 => state8_1707 | 4 => state8_1708 | 5 => state8_1709 | _ => state8_1710

def stree8RLLLLLRR (i : Nat) : State := if i < 6 then stree8RLLLLLRRL i else stree8RLLLLLRRR (i - 6)

def stree8RLLLLLR (i : Nat) : State := if i < 13 then stree8RLLLLLRL i else stree8RLLLLLRR (i - 13)

def stree8RLLLLL (i : Nat) : State := if i < 25 then stree8RLLLLLL i else stree8RLLLLLR (i - 25)

def stree8RLLLLRLLL (i : Nat) : State := match i with | 0 => state8_1711 | 1 => state8_1712 | 2 => state8_1713 | 3 => state8_1714 | 4 => state8_1715 | _ => state8_1716

def stree8RLLLLRLLR (i : Nat) : State := match i with | 0 => state8_1717 | 1 => state8_1718 | 2 => state8_1719 | 3 => state8_1720 | 4 => state8_1721 | 5 => state8_1722 | _ => state8_1723

def stree8RLLLLRLL (i : Nat) : State := if i < 6 then stree8RLLLLRLLL i else stree8RLLLLRLLR (i - 6)

def stree8RLLLLRLRL (i : Nat) : State := match i with | 0 => state8_1724 | 1 => state8_1725 | 2 => state8_1726 | 3 => state8_1727 | 4 => state8_1728 | _ => state8_1729

def stree8RLLLLRLRR (i : Nat) : State := match i with | 0 => state8_1730 | 1 => state8_1731 | 2 => state8_1732 | 3 => state8_1733 | 4 => state8_1734 | 5 => state8_1735 | _ => state8_1736

def stree8RLLLLRLR (i : Nat) : State := if i < 6 then stree8RLLLLRLRL i else stree8RLLLLRLRR (i - 6)

def stree8RLLLLRL (i : Nat) : State := if i < 13 then stree8RLLLLRLL i else stree8RLLLLRLR (i - 13)

def stree8RLLLLRRLL (i : Nat) : State := match i with | 0 => state8_1737 | 1 => state8_1738 | 2 => state8_1739 | 3 => state8_1740 | 4 => state8_1741 | _ => state8_1742

def stree8RLLLLRRLR (i : Nat) : State := match i with | 0 => state8_1743 | 1 => state8_1744 | 2 => state8_1745 | 3 => state8_1746 | 4 => state8_1747 | 5 => state8_1748 | _ => state8_1749

def stree8RLLLLRRL (i : Nat) : State := if i < 6 then stree8RLLLLRRLL i else stree8RLLLLRRLR (i - 6)

def stree8RLLLLRRRL (i : Nat) : State := match i with | 0 => state8_1750 | 1 => state8_1751 | 2 => state8_1752 | 3 => state8_1753 | 4 => state8_1754 | _ => state8_1755

def stree8RLLLLRRRR (i : Nat) : State := match i with | 0 => state8_1756 | 1 => state8_1757 | 2 => state8_1758 | 3 => state8_1759 | 4 => state8_1760 | 5 => state8_1761 | _ => state8_1762

def stree8RLLLLRRR (i : Nat) : State := if i < 6 then stree8RLLLLRRRL i else stree8RLLLLRRRR (i - 6)

def stree8RLLLLRR (i : Nat) : State := if i < 13 then stree8RLLLLRRL i else stree8RLLLLRRR (i - 13)

def stree8RLLLLR (i : Nat) : State := if i < 26 then stree8RLLLLRL i else stree8RLLLLRR (i - 26)

def stree8RLLLL (i : Nat) : State := if i < 51 then stree8RLLLLL i else stree8RLLLLR (i - 51)

def stree8RLLLRLLLL (i : Nat) : State := match i with | 0 => state8_1763 | 1 => state8_1764 | 2 => state8_1765 | 3 => state8_1766 | 4 => state8_1767 | _ => state8_1768

def stree8RLLLRLLLR (i : Nat) : State := match i with | 0 => state8_1769 | 1 => state8_1770 | 2 => state8_1771 | 3 => state8_1772 | 4 => state8_1773 | 5 => state8_1774 | _ => state8_1775

def stree8RLLLRLLL (i : Nat) : State := if i < 6 then stree8RLLLRLLLL i else stree8RLLLRLLLR (i - 6)

def stree8RLLLRLLRL (i : Nat) : State := match i with | 0 => state8_1776 | 1 => state8_1777 | 2 => state8_1778 | 3 => state8_1779 | 4 => state8_1780 | _ => state8_1781

def stree8RLLLRLLRR (i : Nat) : State := match i with | 0 => state8_1782 | 1 => state8_1783 | 2 => state8_1784 | 3 => state8_1785 | 4 => state8_1786 | 5 => state8_1787 | _ => state8_1788

def stree8RLLLRLLR (i : Nat) : State := if i < 6 then stree8RLLLRLLRL i else stree8RLLLRLLRR (i - 6)

def stree8RLLLRLL (i : Nat) : State := if i < 13 then stree8RLLLRLLL i else stree8RLLLRLLR (i - 13)

def stree8RLLLRLRLL (i : Nat) : State := match i with | 0 => state8_1789 | 1 => state8_1790 | 2 => state8_1791 | 3 => state8_1792 | 4 => state8_1793 | _ => state8_1794

def stree8RLLLRLRLR (i : Nat) : State := match i with | 0 => state8_1795 | 1 => state8_1796 | 2 => state8_1797 | 3 => state8_1798 | 4 => state8_1799 | 5 => state8_1800 | _ => state8_1801

def stree8RLLLRLRL (i : Nat) : State := if i < 6 then stree8RLLLRLRLL i else stree8RLLLRLRLR (i - 6)

def stree8RLLLRLRRL (i : Nat) : State := match i with | 0 => state8_1802 | 1 => state8_1803 | 2 => state8_1804 | 3 => state8_1805 | 4 => state8_1806 | _ => state8_1807

def stree8RLLLRLRRR (i : Nat) : State := match i with | 0 => state8_1808 | 1 => state8_1809 | 2 => state8_1810 | 3 => state8_1811 | 4 => state8_1812 | 5 => state8_1813 | _ => state8_1814

def stree8RLLLRLRR (i : Nat) : State := if i < 6 then stree8RLLLRLRRL i else stree8RLLLRLRRR (i - 6)

def stree8RLLLRLR (i : Nat) : State := if i < 13 then stree8RLLLRLRL i else stree8RLLLRLRR (i - 13)

def stree8RLLLRL (i : Nat) : State := if i < 26 then stree8RLLLRLL i else stree8RLLLRLR (i - 26)

def stree8RLLLRRLLL (i : Nat) : State := match i with | 0 => state8_1815 | 1 => state8_1816 | 2 => state8_1817 | 3 => state8_1818 | 4 => state8_1819 | _ => state8_1820

def stree8RLLLRRLLR (i : Nat) : State := match i with | 0 => state8_1821 | 1 => state8_1822 | 2 => state8_1823 | 3 => state8_1824 | 4 => state8_1825 | 5 => state8_1826 | _ => state8_1827

def stree8RLLLRRLL (i : Nat) : State := if i < 6 then stree8RLLLRRLLL i else stree8RLLLRRLLR (i - 6)

def stree8RLLLRRLRL (i : Nat) : State := match i with | 0 => state8_1828 | 1 => state8_1829 | 2 => state8_1830 | 3 => state8_1831 | 4 => state8_1832 | _ => state8_1833

def stree8RLLLRRLRR (i : Nat) : State := match i with | 0 => state8_1834 | 1 => state8_1835 | 2 => state8_1836 | 3 => state8_1837 | 4 => state8_1838 | 5 => state8_1839 | _ => state8_1840

def stree8RLLLRRLR (i : Nat) : State := if i < 6 then stree8RLLLRRLRL i else stree8RLLLRRLRR (i - 6)

def stree8RLLLRRL (i : Nat) : State := if i < 13 then stree8RLLLRRLL i else stree8RLLLRRLR (i - 13)

def stree8RLLLRRRLL (i : Nat) : State := match i with | 0 => state8_1841 | 1 => state8_1842 | 2 => state8_1843 | 3 => state8_1844 | 4 => state8_1845 | _ => state8_1846

def stree8RLLLRRRLR (i : Nat) : State := match i with | 0 => state8_1847 | 1 => state8_1848 | 2 => state8_1849 | 3 => state8_1850 | 4 => state8_1851 | 5 => state8_1852 | _ => state8_1853

def stree8RLLLRRRL (i : Nat) : State := if i < 6 then stree8RLLLRRRLL i else stree8RLLLRRRLR (i - 6)

def stree8RLLLRRRRL (i : Nat) : State := match i with | 0 => state8_1854 | 1 => state8_1855 | 2 => state8_1856 | 3 => state8_1857 | 4 => state8_1858 | _ => state8_1859

def stree8RLLLRRRRR (i : Nat) : State := match i with | 0 => state8_1860 | 1 => state8_1861 | 2 => state8_1862 | 3 => state8_1863 | 4 => state8_1864 | 5 => state8_1865 | _ => state8_1866

def stree8RLLLRRRR (i : Nat) : State := if i < 6 then stree8RLLLRRRRL i else stree8RLLLRRRRR (i - 6)

def stree8RLLLRRR (i : Nat) : State := if i < 13 then stree8RLLLRRRL i else stree8RLLLRRRR (i - 13)

def stree8RLLLRR (i : Nat) : State := if i < 26 then stree8RLLLRRL i else stree8RLLLRRR (i - 26)

def stree8RLLLR (i : Nat) : State := if i < 52 then stree8RLLLRL i else stree8RLLLRR (i - 52)

def stree8RLLL (i : Nat) : State := if i < 103 then stree8RLLLL i else stree8RLLLR (i - 103)

def stree8RLLRLLLLL (i : Nat) : State := match i with | 0 => state8_1867 | 1 => state8_1868 | 2 => state8_1869 | 3 => state8_1870 | 4 => state8_1871 | _ => state8_1872

def stree8RLLRLLLLR (i : Nat) : State := match i with | 0 => state8_1873 | 1 => state8_1874 | 2 => state8_1875 | 3 => state8_1876 | 4 => state8_1877 | 5 => state8_1878 | _ => state8_1879

def stree8RLLRLLLL (i : Nat) : State := if i < 6 then stree8RLLRLLLLL i else stree8RLLRLLLLR (i - 6)

def stree8RLLRLLLRL (i : Nat) : State := match i with | 0 => state8_1880 | 1 => state8_1881 | 2 => state8_1882 | 3 => state8_1883 | 4 => state8_1884 | _ => state8_1885

def stree8RLLRLLLRR (i : Nat) : State := match i with | 0 => state8_1886 | 1 => state8_1887 | 2 => state8_1888 | 3 => state8_1889 | 4 => state8_1890 | 5 => state8_1891 | _ => state8_1892

def stree8RLLRLLLR (i : Nat) : State := if i < 6 then stree8RLLRLLLRL i else stree8RLLRLLLRR (i - 6)

def stree8RLLRLLL (i : Nat) : State := if i < 13 then stree8RLLRLLLL i else stree8RLLRLLLR (i - 13)

def stree8RLLRLLRLL (i : Nat) : State := match i with | 0 => state8_1893 | 1 => state8_1894 | 2 => state8_1895 | 3 => state8_1896 | 4 => state8_1897 | _ => state8_1898

def stree8RLLRLLRLR (i : Nat) : State := match i with | 0 => state8_1899 | 1 => state8_1900 | 2 => state8_1901 | 3 => state8_1902 | 4 => state8_1903 | 5 => state8_1904 | _ => state8_1905

def stree8RLLRLLRL (i : Nat) : State := if i < 6 then stree8RLLRLLRLL i else stree8RLLRLLRLR (i - 6)

def stree8RLLRLLRRL (i : Nat) : State := match i with | 0 => state8_1906 | 1 => state8_1907 | 2 => state8_1908 | 3 => state8_1909 | 4 => state8_1910 | _ => state8_1911

def stree8RLLRLLRRR (i : Nat) : State := match i with | 0 => state8_1912 | 1 => state8_1913 | 2 => state8_1914 | 3 => state8_1915 | 4 => state8_1916 | 5 => state8_1917 | _ => state8_1918

def stree8RLLRLLRR (i : Nat) : State := if i < 6 then stree8RLLRLLRRL i else stree8RLLRLLRRR (i - 6)

def stree8RLLRLLR (i : Nat) : State := if i < 13 then stree8RLLRLLRL i else stree8RLLRLLRR (i - 13)

def stree8RLLRLL (i : Nat) : State := if i < 26 then stree8RLLRLLL i else stree8RLLRLLR (i - 26)

def stree8RLLRLRLLL (i : Nat) : State := match i with | 0 => state8_1919 | 1 => state8_1920 | 2 => state8_1921 | 3 => state8_1922 | 4 => state8_1923 | _ => state8_1924

def stree8RLLRLRLLR (i : Nat) : State := match i with | 0 => state8_1925 | 1 => state8_1926 | 2 => state8_1927 | 3 => state8_1928 | 4 => state8_1929 | 5 => state8_1930 | _ => state8_1931

def stree8RLLRLRLL (i : Nat) : State := if i < 6 then stree8RLLRLRLLL i else stree8RLLRLRLLR (i - 6)

def stree8RLLRLRLRL (i : Nat) : State := match i with | 0 => state8_1932 | 1 => state8_1933 | 2 => state8_1934 | 3 => state8_1935 | 4 => state8_1936 | _ => state8_1937

def stree8RLLRLRLRR (i : Nat) : State := match i with | 0 => state8_1938 | 1 => state8_1939 | 2 => state8_1940 | 3 => state8_1941 | 4 => state8_1942 | 5 => state8_1943 | _ => state8_1944

def stree8RLLRLRLR (i : Nat) : State := if i < 6 then stree8RLLRLRLRL i else stree8RLLRLRLRR (i - 6)

def stree8RLLRLRL (i : Nat) : State := if i < 13 then stree8RLLRLRLL i else stree8RLLRLRLR (i - 13)

def stree8RLLRLRRLL (i : Nat) : State := match i with | 0 => state8_1945 | 1 => state8_1946 | 2 => state8_1947 | 3 => state8_1948 | 4 => state8_1949 | _ => state8_1950

def stree8RLLRLRRLR (i : Nat) : State := match i with | 0 => state8_1951 | 1 => state8_1952 | 2 => state8_1953 | 3 => state8_1954 | 4 => state8_1955 | 5 => state8_1956 | _ => state8_1957

def stree8RLLRLRRL (i : Nat) : State := if i < 6 then stree8RLLRLRRLL i else stree8RLLRLRRLR (i - 6)

def stree8RLLRLRRRL (i : Nat) : State := match i with | 0 => state8_1958 | 1 => state8_1959 | 2 => state8_1960 | 3 => state8_1961 | 4 => state8_1962 | _ => state8_1963

def stree8RLLRLRRRR (i : Nat) : State := match i with | 0 => state8_1964 | 1 => state8_1965 | 2 => state8_1966 | 3 => state8_1967 | 4 => state8_1968 | 5 => state8_1969 | _ => state8_1970

def stree8RLLRLRRR (i : Nat) : State := if i < 6 then stree8RLLRLRRRL i else stree8RLLRLRRRR (i - 6)

def stree8RLLRLRR (i : Nat) : State := if i < 13 then stree8RLLRLRRL i else stree8RLLRLRRR (i - 13)

def stree8RLLRLR (i : Nat) : State := if i < 26 then stree8RLLRLRL i else stree8RLLRLRR (i - 26)

def stree8RLLRL (i : Nat) : State := if i < 52 then stree8RLLRLL i else stree8RLLRLR (i - 52)

def stree8RLLRRLLLL (i : Nat) : State := match i with | 0 => state8_1971 | 1 => state8_1972 | 2 => state8_1973 | 3 => state8_1974 | 4 => state8_1975 | _ => state8_1976

def stree8RLLRRLLLR (i : Nat) : State := match i with | 0 => state8_1977 | 1 => state8_1978 | 2 => state8_1979 | 3 => state8_1980 | 4 => state8_1981 | 5 => state8_1982 | _ => state8_1983

def stree8RLLRRLLL (i : Nat) : State := if i < 6 then stree8RLLRRLLLL i else stree8RLLRRLLLR (i - 6)

def stree8RLLRRLLRL (i : Nat) : State := match i with | 0 => state8_1984 | 1 => state8_1985 | 2 => state8_1986 | 3 => state8_1987 | 4 => state8_1988 | _ => state8_1989

def stree8RLLRRLLRR (i : Nat) : State := match i with | 0 => state8_1990 | 1 => state8_1991 | 2 => state8_1992 | 3 => state8_1993 | 4 => state8_1994 | 5 => state8_1995 | _ => state8_1996

def stree8RLLRRLLR (i : Nat) : State := if i < 6 then stree8RLLRRLLRL i else stree8RLLRRLLRR (i - 6)

def stree8RLLRRLL (i : Nat) : State := if i < 13 then stree8RLLRRLLL i else stree8RLLRRLLR (i - 13)

def stree8RLLRRLRLL (i : Nat) : State := match i with | 0 => state8_1997 | 1 => state8_1998 | 2 => state8_1999 | 3 => state8_2000 | 4 => state8_2001 | _ => state8_2002

def stree8RLLRRLRLR (i : Nat) : State := match i with | 0 => state8_2003 | 1 => state8_2004 | 2 => state8_2005 | 3 => state8_2006 | 4 => state8_2007 | 5 => state8_2008 | _ => state8_2009

def stree8RLLRRLRL (i : Nat) : State := if i < 6 then stree8RLLRRLRLL i else stree8RLLRRLRLR (i - 6)

def stree8RLLRRLRRL (i : Nat) : State := match i with | 0 => state8_2010 | 1 => state8_2011 | 2 => state8_2012 | 3 => state8_2013 | 4 => state8_2014 | _ => state8_2015

def stree8RLLRRLRRR (i : Nat) : State := match i with | 0 => state8_2016 | 1 => state8_2017 | 2 => state8_2018 | 3 => state8_2019 | 4 => state8_2020 | 5 => state8_2021 | _ => state8_2022

def stree8RLLRRLRR (i : Nat) : State := if i < 6 then stree8RLLRRLRRL i else stree8RLLRRLRRR (i - 6)

def stree8RLLRRLR (i : Nat) : State := if i < 13 then stree8RLLRRLRL i else stree8RLLRRLRR (i - 13)

def stree8RLLRRL (i : Nat) : State := if i < 26 then stree8RLLRRLL i else stree8RLLRRLR (i - 26)

def stree8RLLRRRLLL (i : Nat) : State := match i with | 0 => state8_2023 | 1 => state8_2024 | 2 => state8_2025 | 3 => state8_2026 | 4 => state8_2027 | _ => state8_2028

def stree8RLLRRRLLR (i : Nat) : State := match i with | 0 => state8_2029 | 1 => state8_2030 | 2 => state8_2031 | 3 => state8_2032 | 4 => state8_2033 | 5 => state8_2034 | _ => state8_2035

def stree8RLLRRRLL (i : Nat) : State := if i < 6 then stree8RLLRRRLLL i else stree8RLLRRRLLR (i - 6)

def stree8RLLRRRLRL (i : Nat) : State := match i with | 0 => state8_2036 | 1 => state8_2037 | 2 => state8_2038 | 3 => state8_2039 | 4 => state8_2040 | _ => state8_2041

def stree8RLLRRRLRR (i : Nat) : State := match i with | 0 => state8_2042 | 1 => state8_2043 | 2 => state8_2044 | 3 => state8_2045 | 4 => state8_2046 | 5 => state8_2047 | _ => state8_2048

def stree8RLLRRRLR (i : Nat) : State := if i < 6 then stree8RLLRRRLRL i else stree8RLLRRRLRR (i - 6)

def stree8RLLRRRL (i : Nat) : State := if i < 13 then stree8RLLRRRLL i else stree8RLLRRRLR (i - 13)

def stree8RLLRRRRLL (i : Nat) : State := match i with | 0 => state8_2049 | 1 => state8_2050 | 2 => state8_2051 | 3 => state8_2052 | 4 => state8_2053 | _ => state8_2054

def stree8RLLRRRRLR (i : Nat) : State := match i with | 0 => state8_2055 | 1 => state8_2056 | 2 => state8_2057 | 3 => state8_2058 | 4 => state8_2059 | 5 => state8_2060 | _ => state8_2061

def stree8RLLRRRRL (i : Nat) : State := if i < 6 then stree8RLLRRRRLL i else stree8RLLRRRRLR (i - 6)

def stree8RLLRRRRRL (i : Nat) : State := match i with | 0 => state8_2062 | 1 => state8_2063 | 2 => state8_2064 | 3 => state8_2065 | 4 => state8_2066 | _ => state8_2067

def stree8RLLRRRRRR (i : Nat) : State := match i with | 0 => state8_2068 | 1 => state8_2069 | 2 => state8_2070 | 3 => state8_2071 | 4 => state8_2072 | 5 => state8_2073 | _ => state8_2074

def stree8RLLRRRRR (i : Nat) : State := if i < 6 then stree8RLLRRRRRL i else stree8RLLRRRRRR (i - 6)

def stree8RLLRRRR (i : Nat) : State := if i < 13 then stree8RLLRRRRL i else stree8RLLRRRRR (i - 13)

def stree8RLLRRR (i : Nat) : State := if i < 26 then stree8RLLRRRL i else stree8RLLRRRR (i - 26)

def stree8RLLRR (i : Nat) : State := if i < 52 then stree8RLLRRL i else stree8RLLRRR (i - 52)

def stree8RLLR (i : Nat) : State := if i < 104 then stree8RLLRL i else stree8RLLRR (i - 104)

def stree8RLL (i : Nat) : State := if i < 207 then stree8RLLL i else stree8RLLR (i - 207)

def stree8RLRLLLLLL (i : Nat) : State := match i with | 0 => state8_2075 | 1 => state8_2076 | 2 => state8_2077 | 3 => state8_2078 | 4 => state8_2079 | _ => state8_2080

def stree8RLRLLLLLR (i : Nat) : State := match i with | 0 => state8_2081 | 1 => state8_2082 | 2 => state8_2083 | 3 => state8_2084 | 4 => state8_2085 | _ => state8_2086

def stree8RLRLLLLL (i : Nat) : State := if i < 6 then stree8RLRLLLLLL i else stree8RLRLLLLLR (i - 6)

def stree8RLRLLLLRL (i : Nat) : State := match i with | 0 => state8_2087 | 1 => state8_2088 | 2 => state8_2089 | 3 => state8_2090 | 4 => state8_2091 | _ => state8_2092

def stree8RLRLLLLRR (i : Nat) : State := match i with | 0 => state8_2093 | 1 => state8_2094 | 2 => state8_2095 | 3 => state8_2096 | 4 => state8_2097 | 5 => state8_2098 | _ => state8_2099

def stree8RLRLLLLR (i : Nat) : State := if i < 6 then stree8RLRLLLLRL i else stree8RLRLLLLRR (i - 6)

def stree8RLRLLLL (i : Nat) : State := if i < 12 then stree8RLRLLLLL i else stree8RLRLLLLR (i - 12)

def stree8RLRLLLRLL (i : Nat) : State := match i with | 0 => state8_2100 | 1 => state8_2101 | 2 => state8_2102 | 3 => state8_2103 | 4 => state8_2104 | _ => state8_2105

def stree8RLRLLLRLR (i : Nat) : State := match i with | 0 => state8_2106 | 1 => state8_2107 | 2 => state8_2108 | 3 => state8_2109 | 4 => state8_2110 | 5 => state8_2111 | _ => state8_2112

def stree8RLRLLLRL (i : Nat) : State := if i < 6 then stree8RLRLLLRLL i else stree8RLRLLLRLR (i - 6)

def stree8RLRLLLRRL (i : Nat) : State := match i with | 0 => state8_2113 | 1 => state8_2114 | 2 => state8_2115 | 3 => state8_2116 | 4 => state8_2117 | _ => state8_2118

def stree8RLRLLLRRR (i : Nat) : State := match i with | 0 => state8_2119 | 1 => state8_2120 | 2 => state8_2121 | 3 => state8_2122 | 4 => state8_2123 | 5 => state8_2124 | _ => state8_2125

def stree8RLRLLLRR (i : Nat) : State := if i < 6 then stree8RLRLLLRRL i else stree8RLRLLLRRR (i - 6)

def stree8RLRLLLR (i : Nat) : State := if i < 13 then stree8RLRLLLRL i else stree8RLRLLLRR (i - 13)

def stree8RLRLLL (i : Nat) : State := if i < 25 then stree8RLRLLLL i else stree8RLRLLLR (i - 25)

def stree8RLRLLRLLL (i : Nat) : State := match i with | 0 => state8_2126 | 1 => state8_2127 | 2 => state8_2128 | 3 => state8_2129 | 4 => state8_2130 | _ => state8_2131

def stree8RLRLLRLLR (i : Nat) : State := match i with | 0 => state8_2132 | 1 => state8_2133 | 2 => state8_2134 | 3 => state8_2135 | 4 => state8_2136 | 5 => state8_2137 | _ => state8_2138

def stree8RLRLLRLL (i : Nat) : State := if i < 6 then stree8RLRLLRLLL i else stree8RLRLLRLLR (i - 6)

def stree8RLRLLRLRL (i : Nat) : State := match i with | 0 => state8_2139 | 1 => state8_2140 | 2 => state8_2141 | 3 => state8_2142 | 4 => state8_2143 | _ => state8_2144

def stree8RLRLLRLRR (i : Nat) : State := match i with | 0 => state8_2145 | 1 => state8_2146 | 2 => state8_2147 | 3 => state8_2148 | 4 => state8_2149 | 5 => state8_2150 | _ => state8_2151

def stree8RLRLLRLR (i : Nat) : State := if i < 6 then stree8RLRLLRLRL i else stree8RLRLLRLRR (i - 6)

def stree8RLRLLRL (i : Nat) : State := if i < 13 then stree8RLRLLRLL i else stree8RLRLLRLR (i - 13)

def stree8RLRLLRRLL (i : Nat) : State := match i with | 0 => state8_2152 | 1 => state8_2153 | 2 => state8_2154 | 3 => state8_2155 | 4 => state8_2156 | _ => state8_2157

def stree8RLRLLRRLR (i : Nat) : State := match i with | 0 => state8_2158 | 1 => state8_2159 | 2 => state8_2160 | 3 => state8_2161 | 4 => state8_2162 | 5 => state8_2163 | _ => state8_2164

def stree8RLRLLRRL (i : Nat) : State := if i < 6 then stree8RLRLLRRLL i else stree8RLRLLRRLR (i - 6)

def stree8RLRLLRRRL (i : Nat) : State := match i with | 0 => state8_2165 | 1 => state8_2166 | 2 => state8_2167 | 3 => state8_2168 | 4 => state8_2169 | _ => state8_2170

def stree8RLRLLRRRR (i : Nat) : State := match i with | 0 => state8_2171 | 1 => state8_2172 | 2 => state8_2173 | 3 => state8_2174 | 4 => state8_2175 | 5 => state8_2176 | _ => state8_2177

def stree8RLRLLRRR (i : Nat) : State := if i < 6 then stree8RLRLLRRRL i else stree8RLRLLRRRR (i - 6)

def stree8RLRLLRR (i : Nat) : State := if i < 13 then stree8RLRLLRRL i else stree8RLRLLRRR (i - 13)

def stree8RLRLLR (i : Nat) : State := if i < 26 then stree8RLRLLRL i else stree8RLRLLRR (i - 26)

def stree8RLRLL (i : Nat) : State := if i < 51 then stree8RLRLLL i else stree8RLRLLR (i - 51)

def stree8RLRLRLLLL (i : Nat) : State := match i with | 0 => state8_2178 | 1 => state8_2179 | 2 => state8_2180 | 3 => state8_2181 | 4 => state8_2182 | _ => state8_2183

def stree8RLRLRLLLR (i : Nat) : State := match i with | 0 => state8_2184 | 1 => state8_2185 | 2 => state8_2186 | 3 => state8_2187 | 4 => state8_2188 | 5 => state8_2189 | _ => state8_2190

def stree8RLRLRLLL (i : Nat) : State := if i < 6 then stree8RLRLRLLLL i else stree8RLRLRLLLR (i - 6)

def stree8RLRLRLLRL (i : Nat) : State := match i with | 0 => state8_2191 | 1 => state8_2192 | 2 => state8_2193 | 3 => state8_2194 | 4 => state8_2195 | _ => state8_2196

def stree8RLRLRLLRR (i : Nat) : State := match i with | 0 => state8_2197 | 1 => state8_2198 | 2 => state8_2199 | 3 => state8_2200 | 4 => state8_2201 | 5 => state8_2202 | _ => state8_2203

def stree8RLRLRLLR (i : Nat) : State := if i < 6 then stree8RLRLRLLRL i else stree8RLRLRLLRR (i - 6)

def stree8RLRLRLL (i : Nat) : State := if i < 13 then stree8RLRLRLLL i else stree8RLRLRLLR (i - 13)

def stree8RLRLRLRLL (i : Nat) : State := match i with | 0 => state8_2204 | 1 => state8_2205 | 2 => state8_2206 | 3 => state8_2207 | 4 => state8_2208 | _ => state8_2209

def stree8RLRLRLRLR (i : Nat) : State := match i with | 0 => state8_2210 | 1 => state8_2211 | 2 => state8_2212 | 3 => state8_2213 | 4 => state8_2214 | 5 => state8_2215 | _ => state8_2216

def stree8RLRLRLRL (i : Nat) : State := if i < 6 then stree8RLRLRLRLL i else stree8RLRLRLRLR (i - 6)

def stree8RLRLRLRRL (i : Nat) : State := match i with | 0 => state8_2217 | 1 => state8_2218 | 2 => state8_2219 | 3 => state8_2220 | 4 => state8_2221 | _ => state8_2222

def stree8RLRLRLRRR (i : Nat) : State := match i with | 0 => state8_2223 | 1 => state8_2224 | 2 => state8_2225 | 3 => state8_2226 | 4 => state8_2227 | 5 => state8_2228 | _ => state8_2229

def stree8RLRLRLRR (i : Nat) : State := if i < 6 then stree8RLRLRLRRL i else stree8RLRLRLRRR (i - 6)

def stree8RLRLRLR (i : Nat) : State := if i < 13 then stree8RLRLRLRL i else stree8RLRLRLRR (i - 13)

def stree8RLRLRL (i : Nat) : State := if i < 26 then stree8RLRLRLL i else stree8RLRLRLR (i - 26)

def stree8RLRLRRLLL (i : Nat) : State := match i with | 0 => state8_2230 | 1 => state8_2231 | 2 => state8_2232 | 3 => state8_2233 | 4 => state8_2234 | _ => state8_2235

def stree8RLRLRRLLR (i : Nat) : State := match i with | 0 => state8_2236 | 1 => state8_2237 | 2 => state8_2238 | 3 => state8_2239 | 4 => state8_2240 | 5 => state8_2241 | _ => state8_2242

def stree8RLRLRRLL (i : Nat) : State := if i < 6 then stree8RLRLRRLLL i else stree8RLRLRRLLR (i - 6)

def stree8RLRLRRLRL (i : Nat) : State := match i with | 0 => state8_2243 | 1 => state8_2244 | 2 => state8_2245 | 3 => state8_2246 | 4 => state8_2247 | _ => state8_2248

def stree8RLRLRRLRR (i : Nat) : State := match i with | 0 => state8_2249 | 1 => state8_2250 | 2 => state8_2251 | 3 => state8_2252 | 4 => state8_2253 | 5 => state8_2254 | _ => state8_2255

def stree8RLRLRRLR (i : Nat) : State := if i < 6 then stree8RLRLRRLRL i else stree8RLRLRRLRR (i - 6)

def stree8RLRLRRL (i : Nat) : State := if i < 13 then stree8RLRLRRLL i else stree8RLRLRRLR (i - 13)

def stree8RLRLRRRLL (i : Nat) : State := match i with | 0 => state8_2256 | 1 => state8_2257 | 2 => state8_2258 | 3 => state8_2259 | 4 => state8_2260 | _ => state8_2261

def stree8RLRLRRRLR (i : Nat) : State := match i with | 0 => state8_2262 | 1 => state8_2263 | 2 => state8_2264 | 3 => state8_2265 | 4 => state8_2266 | 5 => state8_2267 | _ => state8_2268

def stree8RLRLRRRL (i : Nat) : State := if i < 6 then stree8RLRLRRRLL i else stree8RLRLRRRLR (i - 6)

def stree8RLRLRRRRL (i : Nat) : State := match i with | 0 => state8_2269 | 1 => state8_2270 | 2 => state8_2271 | 3 => state8_2272 | 4 => state8_2273 | _ => state8_2274

def stree8RLRLRRRRR (i : Nat) : State := match i with | 0 => state8_2275 | 1 => state8_2276 | 2 => state8_2277 | 3 => state8_2278 | 4 => state8_2279 | 5 => state8_2280 | _ => state8_2281

def stree8RLRLRRRR (i : Nat) : State := if i < 6 then stree8RLRLRRRRL i else stree8RLRLRRRRR (i - 6)

def stree8RLRLRRR (i : Nat) : State := if i < 13 then stree8RLRLRRRL i else stree8RLRLRRRR (i - 13)

def stree8RLRLRR (i : Nat) : State := if i < 26 then stree8RLRLRRL i else stree8RLRLRRR (i - 26)

def stree8RLRLR (i : Nat) : State := if i < 52 then stree8RLRLRL i else stree8RLRLRR (i - 52)

def stree8RLRL (i : Nat) : State := if i < 103 then stree8RLRLL i else stree8RLRLR (i - 103)

def stree8RLRRLLLLL (i : Nat) : State := match i with | 0 => state8_2282 | 1 => state8_2283 | 2 => state8_2284 | 3 => state8_2285 | 4 => state8_2286 | _ => state8_2287

def stree8RLRRLLLLR (i : Nat) : State := match i with | 0 => state8_2288 | 1 => state8_2289 | 2 => state8_2290 | 3 => state8_2291 | 4 => state8_2292 | 5 => state8_2293 | _ => state8_2294

def stree8RLRRLLLL (i : Nat) : State := if i < 6 then stree8RLRRLLLLL i else stree8RLRRLLLLR (i - 6)

def stree8RLRRLLLRL (i : Nat) : State := match i with | 0 => state8_2295 | 1 => state8_2296 | 2 => state8_2297 | 3 => state8_2298 | 4 => state8_2299 | _ => state8_2300

def stree8RLRRLLLRR (i : Nat) : State := match i with | 0 => state8_2301 | 1 => state8_2302 | 2 => state8_2303 | 3 => state8_2304 | 4 => state8_2305 | 5 => state8_2306 | _ => state8_2307

def stree8RLRRLLLR (i : Nat) : State := if i < 6 then stree8RLRRLLLRL i else stree8RLRRLLLRR (i - 6)

def stree8RLRRLLL (i : Nat) : State := if i < 13 then stree8RLRRLLLL i else stree8RLRRLLLR (i - 13)

def stree8RLRRLLRLL (i : Nat) : State := match i with | 0 => state8_2308 | 1 => state8_2309 | 2 => state8_2310 | 3 => state8_2311 | 4 => state8_2312 | _ => state8_2313

def stree8RLRRLLRLR (i : Nat) : State := match i with | 0 => state8_2314 | 1 => state8_2315 | 2 => state8_2316 | 3 => state8_2317 | 4 => state8_2318 | 5 => state8_2319 | _ => state8_2320

def stree8RLRRLLRL (i : Nat) : State := if i < 6 then stree8RLRRLLRLL i else stree8RLRRLLRLR (i - 6)

def stree8RLRRLLRRL (i : Nat) : State := match i with | 0 => state8_2321 | 1 => state8_2322 | 2 => state8_2323 | 3 => state8_2324 | 4 => state8_2325 | _ => state8_2326

def stree8RLRRLLRRR (i : Nat) : State := match i with | 0 => state8_2327 | 1 => state8_2328 | 2 => state8_2329 | 3 => state8_2330 | 4 => state8_2331 | 5 => state8_2332 | _ => state8_2333

def stree8RLRRLLRR (i : Nat) : State := if i < 6 then stree8RLRRLLRRL i else stree8RLRRLLRRR (i - 6)

def stree8RLRRLLR (i : Nat) : State := if i < 13 then stree8RLRRLLRL i else stree8RLRRLLRR (i - 13)

def stree8RLRRLL (i : Nat) : State := if i < 26 then stree8RLRRLLL i else stree8RLRRLLR (i - 26)

def stree8RLRRLRLLL (i : Nat) : State := match i with | 0 => state8_2334 | 1 => state8_2335 | 2 => state8_2336 | 3 => state8_2337 | 4 => state8_2338 | _ => state8_2339

def stree8RLRRLRLLR (i : Nat) : State := match i with | 0 => state8_2340 | 1 => state8_2341 | 2 => state8_2342 | 3 => state8_2343 | 4 => state8_2344 | 5 => state8_2345 | _ => state8_2346

def stree8RLRRLRLL (i : Nat) : State := if i < 6 then stree8RLRRLRLLL i else stree8RLRRLRLLR (i - 6)

def stree8RLRRLRLRL (i : Nat) : State := match i with | 0 => state8_2347 | 1 => state8_2348 | 2 => state8_2349 | 3 => state8_2350 | 4 => state8_2351 | _ => state8_2352

def stree8RLRRLRLRR (i : Nat) : State := match i with | 0 => state8_2353 | 1 => state8_2354 | 2 => state8_2355 | 3 => state8_2356 | 4 => state8_2357 | 5 => state8_2358 | _ => state8_2359

def stree8RLRRLRLR (i : Nat) : State := if i < 6 then stree8RLRRLRLRL i else stree8RLRRLRLRR (i - 6)

def stree8RLRRLRL (i : Nat) : State := if i < 13 then stree8RLRRLRLL i else stree8RLRRLRLR (i - 13)

def stree8RLRRLRRLL (i : Nat) : State := match i with | 0 => state8_2360 | 1 => state8_2361 | 2 => state8_2362 | 3 => state8_2363 | 4 => state8_2364 | _ => state8_2365

def stree8RLRRLRRLR (i : Nat) : State := match i with | 0 => state8_2366 | 1 => state8_2367 | 2 => state8_2368 | 3 => state8_2369 | 4 => state8_2370 | 5 => state8_2371 | _ => state8_2372

def stree8RLRRLRRL (i : Nat) : State := if i < 6 then stree8RLRRLRRLL i else stree8RLRRLRRLR (i - 6)

def stree8RLRRLRRRL (i : Nat) : State := match i with | 0 => state8_2373 | 1 => state8_2374 | 2 => state8_2375 | 3 => state8_2376 | 4 => state8_2377 | _ => state8_2378

def stree8RLRRLRRRR (i : Nat) : State := match i with | 0 => state8_2379 | 1 => state8_2380 | 2 => state8_2381 | 3 => state8_2382 | 4 => state8_2383 | 5 => state8_2384 | _ => state8_2385

def stree8RLRRLRRR (i : Nat) : State := if i < 6 then stree8RLRRLRRRL i else stree8RLRRLRRRR (i - 6)

def stree8RLRRLRR (i : Nat) : State := if i < 13 then stree8RLRRLRRL i else stree8RLRRLRRR (i - 13)

def stree8RLRRLR (i : Nat) : State := if i < 26 then stree8RLRRLRL i else stree8RLRRLRR (i - 26)

def stree8RLRRL (i : Nat) : State := if i < 52 then stree8RLRRLL i else stree8RLRRLR (i - 52)

def stree8RLRRRLLLL (i : Nat) : State := match i with | 0 => state8_2386 | 1 => state8_2387 | 2 => state8_2388 | 3 => state8_2389 | 4 => state8_2390 | _ => state8_2391

def stree8RLRRRLLLR (i : Nat) : State := match i with | 0 => state8_2392 | 1 => state8_2393 | 2 => state8_2394 | 3 => state8_2395 | 4 => state8_2396 | 5 => state8_2397 | _ => state8_2398

def stree8RLRRRLLL (i : Nat) : State := if i < 6 then stree8RLRRRLLLL i else stree8RLRRRLLLR (i - 6)

def stree8RLRRRLLRL (i : Nat) : State := match i with | 0 => state8_2399 | 1 => state8_2400 | 2 => state8_2401 | 3 => state8_2402 | 4 => state8_2403 | _ => state8_2404

def stree8RLRRRLLRR (i : Nat) : State := match i with | 0 => state8_2405 | 1 => state8_2406 | 2 => state8_2407 | 3 => state8_2408 | 4 => state8_2409 | 5 => state8_2410 | _ => state8_2411

def stree8RLRRRLLR (i : Nat) : State := if i < 6 then stree8RLRRRLLRL i else stree8RLRRRLLRR (i - 6)

def stree8RLRRRLL (i : Nat) : State := if i < 13 then stree8RLRRRLLL i else stree8RLRRRLLR (i - 13)

def stree8RLRRRLRLL (i : Nat) : State := match i with | 0 => state8_2412 | 1 => state8_2413 | 2 => state8_2414 | 3 => state8_2415 | 4 => state8_2416 | _ => state8_2417

def stree8RLRRRLRLR (i : Nat) : State := match i with | 0 => state8_2418 | 1 => state8_2419 | 2 => state8_2420 | 3 => state8_2421 | 4 => state8_2422 | 5 => state8_2423 | _ => state8_2424

def stree8RLRRRLRL (i : Nat) : State := if i < 6 then stree8RLRRRLRLL i else stree8RLRRRLRLR (i - 6)

def stree8RLRRRLRRL (i : Nat) : State := match i with | 0 => state8_2425 | 1 => state8_2426 | 2 => state8_2427 | 3 => state8_2428 | 4 => state8_2429 | _ => state8_2430

def stree8RLRRRLRRR (i : Nat) : State := match i with | 0 => state8_2431 | 1 => state8_2432 | 2 => state8_2433 | 3 => state8_2434 | 4 => state8_2435 | 5 => state8_2436 | _ => state8_2437

def stree8RLRRRLRR (i : Nat) : State := if i < 6 then stree8RLRRRLRRL i else stree8RLRRRLRRR (i - 6)

def stree8RLRRRLR (i : Nat) : State := if i < 13 then stree8RLRRRLRL i else stree8RLRRRLRR (i - 13)

def stree8RLRRRL (i : Nat) : State := if i < 26 then stree8RLRRRLL i else stree8RLRRRLR (i - 26)

def stree8RLRRRRLLL (i : Nat) : State := match i with | 0 => state8_2438 | 1 => state8_2439 | 2 => state8_2440 | 3 => state8_2441 | 4 => state8_2442 | _ => state8_2443

def stree8RLRRRRLLR (i : Nat) : State := match i with | 0 => state8_2444 | 1 => state8_2445 | 2 => state8_2446 | 3 => state8_2447 | 4 => state8_2448 | 5 => state8_2449 | _ => state8_2450

def stree8RLRRRRLL (i : Nat) : State := if i < 6 then stree8RLRRRRLLL i else stree8RLRRRRLLR (i - 6)

def stree8RLRRRRLRL (i : Nat) : State := match i with | 0 => state8_2451 | 1 => state8_2452 | 2 => state8_2453 | 3 => state8_2454 | 4 => state8_2455 | _ => state8_2456

def stree8RLRRRRLRR (i : Nat) : State := match i with | 0 => state8_2457 | 1 => state8_2458 | 2 => state8_2459 | 3 => state8_2460 | 4 => state8_2461 | 5 => state8_2462 | _ => state8_2463

def stree8RLRRRRLR (i : Nat) : State := if i < 6 then stree8RLRRRRLRL i else stree8RLRRRRLRR (i - 6)

def stree8RLRRRRL (i : Nat) : State := if i < 13 then stree8RLRRRRLL i else stree8RLRRRRLR (i - 13)

def stree8RLRRRRRLL (i : Nat) : State := match i with | 0 => state8_2464 | 1 => state8_2465 | 2 => state8_2466 | 3 => state8_2467 | 4 => state8_2468 | _ => state8_2469

def stree8RLRRRRRLR (i : Nat) : State := match i with | 0 => state8_2470 | 1 => state8_2471 | 2 => state8_2472 | 3 => state8_2473 | 4 => state8_2474 | 5 => state8_2475 | _ => state8_2476

def stree8RLRRRRRL (i : Nat) : State := if i < 6 then stree8RLRRRRRLL i else stree8RLRRRRRLR (i - 6)

def stree8RLRRRRRRL (i : Nat) : State := match i with | 0 => state8_2477 | 1 => state8_2478 | 2 => state8_2479 | 3 => state8_2480 | 4 => state8_2481 | _ => state8_2482

def stree8RLRRRRRRR (i : Nat) : State := match i with | 0 => state8_2483 | 1 => state8_2484 | 2 => state8_2485 | 3 => state8_2486 | 4 => state8_2487 | 5 => state8_2488 | _ => state8_2489

def stree8RLRRRRRR (i : Nat) : State := if i < 6 then stree8RLRRRRRRL i else stree8RLRRRRRRR (i - 6)

def stree8RLRRRRR (i : Nat) : State := if i < 13 then stree8RLRRRRRL i else stree8RLRRRRRR (i - 13)

def stree8RLRRRR (i : Nat) : State := if i < 26 then stree8RLRRRRL i else stree8RLRRRRR (i - 26)

def stree8RLRRR (i : Nat) : State := if i < 52 then stree8RLRRRL i else stree8RLRRRR (i - 52)

def stree8RLRR (i : Nat) : State := if i < 104 then stree8RLRRL i else stree8RLRRR (i - 104)

def stree8RLR (i : Nat) : State := if i < 207 then stree8RLRL i else stree8RLRR (i - 207)

def stree8RL (i : Nat) : State := if i < 415 then stree8RLL i else stree8RLR (i - 415)

def stree8RRLLLLLLL (i : Nat) : State := match i with | 0 => state8_2490 | 1 => state8_2491 | 2 => state8_2492 | 3 => state8_2493 | 4 => state8_2494 | _ => state8_2495

def stree8RRLLLLLLR (i : Nat) : State := match i with | 0 => state8_2496 | 1 => state8_2497 | 2 => state8_2498 | 3 => state8_2499 | 4 => state8_2500 | _ => state8_2501

def stree8RRLLLLLL (i : Nat) : State := if i < 6 then stree8RRLLLLLLL i else stree8RRLLLLLLR (i - 6)

def stree8RRLLLLLRL (i : Nat) : State := match i with | 0 => state8_2502 | 1 => state8_2503 | 2 => state8_2504 | 3 => state8_2505 | 4 => state8_2506 | _ => state8_2507

def stree8RRLLLLLRR (i : Nat) : State := match i with | 0 => state8_2508 | 1 => state8_2509 | 2 => state8_2510 | 3 => state8_2511 | 4 => state8_2512 | 5 => state8_2513 | _ => state8_2514

def stree8RRLLLLLR (i : Nat) : State := if i < 6 then stree8RRLLLLLRL i else stree8RRLLLLLRR (i - 6)

def stree8RRLLLLL (i : Nat) : State := if i < 12 then stree8RRLLLLLL i else stree8RRLLLLLR (i - 12)

def stree8RRLLLLRLL (i : Nat) : State := match i with | 0 => state8_2515 | 1 => state8_2516 | 2 => state8_2517 | 3 => state8_2518 | 4 => state8_2519 | _ => state8_2520

def stree8RRLLLLRLR (i : Nat) : State := match i with | 0 => state8_2521 | 1 => state8_2522 | 2 => state8_2523 | 3 => state8_2524 | 4 => state8_2525 | 5 => state8_2526 | _ => state8_2527

end Paper2.Certificates.Q6.Coverage
