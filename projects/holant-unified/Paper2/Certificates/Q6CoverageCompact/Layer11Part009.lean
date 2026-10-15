import Paper2.Certificates.Q6CoverageCompact.Layer11Part008

namespace Paper2.Certificates.Q6.Coverage

def ntree11LRRRRLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1505,by decide⟩,⟨1505,by decide⟩,⟨1313,by decide⟩] | 1 => ![⟨1506,by decide⟩,⟨163,by decide⟩,⟨1317,by decide⟩] | 2 => ![⟨1507,by decide⟩,⟨1313,by decide⟩,⟨1313,by decide⟩] | 3 => ![⟨1508,by decide⟩,⟨1502,by decide⟩,⟨1320,by decide⟩] | 4 => ![⟨1509,by decide⟩,⟨161,by decide⟩,⟨1320,by decide⟩] | 5 => ![⟨1510,by decide⟩,⟨163,by decide⟩,⟨1322,by decide⟩] | _ => ![⟨1511,by decide⟩,⟨1504,by decide⟩,⟨1322,by decide⟩]

def ntree11LRRRRLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1512,by decide⟩,⟨1505,by decide⟩,⟨1323,by decide⟩] | 1 => ![⟨1513,by decide⟩,⟨1514,by decide⟩,⟨1322,by decide⟩] | 2 => ![⟨1515,by decide⟩,⟨174,by decide⟩,⟨1322,by decide⟩] | 3 => ![⟨1516,by decide⟩,⟨177,by decide⟩,⟨1327,by decide⟩] | 4 => ![⟨1514,by decide⟩,⟨1514,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨1517,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨1518,by decide⟩,⟨1519,by decide⟩] | _ => ![⟨163,by decide⟩,⟨1520,by decide⟩,⟨1521,by decide⟩]

def ntree11LRRRRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRRRRLLLL i else ntree11LRRRRLLLR (i - 7)

def ntree11LRRRRLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1330,by decide⟩,⟨1517,by decide⟩,⟨1330,by decide⟩] | 1 => ![⟨1522,by decide⟩,⟨163,by decide⟩,⟨1330,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨1521,by decide⟩,⟨1521,by decide⟩] | 3 => ![⟨167,by decide⟩,⟨1523,by decide⟩,⟨1524,by decide⟩] | 4 => ![⟨1322,by decide⟩,⟨1521,by decide⟩,⟨1525,by decide⟩] | 5 => ![⟨1526,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨1494,by decide⟩,⟨1494,by decide⟩] | _ => ![⟨1527,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LRRRRLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1528,by decide⟩,⟨1313,by decide⟩,⟨1313,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1529,by decide⟩] | 2 => ![⟨1530,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1531,by decide⟩,⟨10,by decide⟩,⟨1338,by decide⟩] | 4 => ![⟨1532,by decide⟩,⟨196,by decide⟩,⟨1335,by decide⟩] | 5 => ![⟨1533,by decide⟩,⟨10,by decide⟩,⟨1338,by decide⟩] | 6 => ![⟨1534,by decide⟩,⟨1535,by decide⟩,⟨1340,by decide⟩] | _ => ![⟨1536,by decide⟩,⟨196,by decide⟩,⟨1320,by decide⟩]

def ntree11LRRRRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRRRRLLRL i else ntree11LRRRRLLRR (i - 8)

def ntree11LRRRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRRRRLLL i else ntree11LRRRRLLR (i - 15)

def ntree11LRRRRLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1537,by decide⟩,⟨201,by decide⟩,⟨1322,by decide⟩] | 1 => ![⟨1538,by decide⟩,⟨1535,by decide⟩,⟨1323,by decide⟩] | 2 => ![⟨1539,by decide⟩,⟨206,by decide⟩,⟨1322,by decide⟩] | 3 => ![⟨1540,by decide⟩,⟨209,by decide⟩,⟨1350,by decide⟩] | 4 => ![⟨47,by decide⟩,⟨1517,by decide⟩,⟨47,by decide⟩] | 5 => ![⟨1541,by decide⟩,⟨201,by decide⟩,⟨1354,by decide⟩] | _ => ![⟨1322,by decide⟩,⟨1542,by decide⟩,⟨1322,by decide⟩]

def ntree11LRRRRLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1322,by decide⟩,⟨212,by decide⟩,⟨1543,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨1544,by decide⟩,⟨1544,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨1544,by decide⟩,⟨1544,by decide⟩] | 3 => ![⟨1527,by decide⟩,⟨1544,by decide⟩,⟨1544,by decide⟩] | 4 => ![⟨1530,by decide⟩,⟨10,by decide⟩,⟨1500,by decide⟩] | 5 => ![⟨1545,by decide⟩,⟨1502,by decide⟩,⟨44,by decide⟩] | 6 => ![⟨1546,by decide⟩,⟨161,by decide⟩,⟨1335,by decide⟩] | _ => ![⟨1547,by decide⟩,⟨1504,by decide⟩,⟨1338,by decide⟩]

def ntree11LRRRRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRRRRLRLL i else ntree11LRRRRLRLR (i - 7)

def ntree11LRRRRLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1548,by decide⟩,⟨1505,by decide⟩,⟨1340,by decide⟩] | 1 => ![⟨1549,by decide⟩,⟨1514,by decide⟩,⟨47,by decide⟩] | 2 => ![⟨1550,by decide⟩,⟨174,by decide⟩,⟨1338,by decide⟩] | 3 => ![⟨163,by decide⟩,⟨1551,by decide⟩,⟨212,by decide⟩] | 4 => ![⟨1552,by decide⟩,⟨163,by decide⟩,⟨1354,by decide⟩] | 5 => ![⟨226,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨1553,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1554,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LRRRRLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨1398,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨1555,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1556,by decide⟩,⟨1382,by decide⟩,⟨1382,by decide⟩] | 3 => ![⟨1555,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨1492,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1557,by decide⟩,⟨1384,by decide⟩,⟨1384,by decide⟩] | 6 => ![⟨1558,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1493,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11LRRRRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRRRRLRRL i else ntree11LRRRRLRRR (i - 8)

def ntree11LRRRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRRRRLRL i else ntree11LRRRRLRR (i - 15)

def ntree11LRRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LRRRRLL i else ntree11LRRRRLR (i - 31)

def ntree11LRRRRRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1558,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨1559,by decide⟩,⟨1559,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨1399,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1560,by decide⟩] | 4 => ![⟨1561,by decide⟩,⟨1393,by decide⟩,⟨1393,by decide⟩] | 5 => ![⟨1499,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨161,by decide⟩,⟨161,by decide⟩,⟨0,by decide⟩]

def ntree11LRRRRRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨163,by decide⟩,⟨163,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨163,by decide⟩,⟨1562,by decide⟩,⟨1563,by decide⟩] | 2 => ![⟨167,by decide⟩,⟨1564,by decide⟩,⟨1563,by decide⟩] | 3 => ![⟨1509,by decide⟩,⟨247,by decide⟩,⟨1320,by decide⟩] | 4 => ![⟨1510,by decide⟩,⟨248,by decide⟩,⟨1322,by decide⟩] | 5 => ![⟨1515,by decide⟩,⟨250,by decide⟩,⟨1322,by decide⟩] | 6 => ![⟨1322,by decide⟩,⟨1565,by decide⟩,⟨1566,by decide⟩] | _ => ![⟨10,by decide⟩,⟨1567,by decide⟩,⟨1568,by decide⟩]

def ntree11LRRRRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRRRRRLLL i else ntree11LRRRRRLLR (i - 7)

def ntree11LRRRRRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1569,by decide⟩,⟨1569,by decide⟩,⟨1384,by decide⟩] | 1 => ![⟨263,by decide⟩,⟨263,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1570,by decide⟩,⟨163,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1571,by decide⟩,⟨1384,by decide⟩,⟨1384,by decide⟩] | 4 => ![⟨167,by decide⟩,⟨1567,by decide⟩,⟨1572,by decide⟩] | 5 => ![⟨1573,by decide⟩,⟨263,by decide⟩,⟨1322,by decide⟩] | 6 => ![⟨1574,by decide⟩,⟨1569,by decide⟩,⟨1404,by decide⟩] | _ => ![⟨1573,by decide⟩,⟨266,by decide⟩,⟨1322,by decide⟩]

def ntree11LRRRRRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1575,by decide⟩,⟨1559,by decide⟩,⟨1322,by decide⟩] | 1 => ![⟨1526,by decide⟩,⟨268,by decide⟩,⟨268,by decide⟩] | 2 => ![⟨1527,by decide⟩,⟨270,by decide⟩,⟨270,by decide⟩] | 3 => ![⟨1576,by decide⟩,⟨1577,by decide⟩,⟨47,by decide⟩] | 4 => ![⟨1558,by decide⟩,⟨1418,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1530,by decide⟩,⟨270,by decide⟩,⟨270,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1578,by decide⟩] | _ => ![⟨196,by decide⟩,⟨196,by decide⟩,⟨1578,by decide⟩]

def ntree11LRRRRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRRRRRLRL i else ntree11LRRRRRLRR (i - 8)

def ntree11LRRRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRRRRRLL i else ntree11LRRRRRLR (i - 15)

def ntree11LRRRRRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1579,by decide⟩] | 1 => ![⟨47,by decide⟩,⟨1580,by decide⟩,⟨1581,by decide⟩] | 2 => ![⟨167,by decide⟩,⟨1414,by decide⟩,⟨1579,by decide⟩] | 3 => ![⟨199,by decide⟩,⟨1582,by decide⟩,⟨1581,by decide⟩] | 4 => ![⟨1320,by decide⟩,⟨268,by decide⟩,⟨1583,by decide⟩] | 5 => ![⟨1536,by decide⟩,⟨280,by decide⟩,⟨1583,by decide⟩] | _ => ![⟨1322,by decide⟩,⟨270,by decide⟩,⟨1584,by decide⟩]

def ntree11LRRRRRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1537,by decide⟩,⟨281,by decide⟩,⟨1584,by decide⟩] | 1 => ![⟨1539,by decide⟩,⟨283,by decide⟩,⟨1584,by decide⟩] | 2 => ![⟨1346,by decide⟩,⟨1585,by decide⟩,⟨1586,by decide⟩] | 3 => ![⟨263,by decide⟩,⟨1587,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨201,by decide⟩,⟨201,by decide⟩,⟨1579,by decide⟩] | 5 => ![⟨1588,by decide⟩,⟨1589,by decide⟩,⟨1346,by decide⟩] | 6 => ![⟨1590,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1590,by decide⟩,⟨268,by decide⟩,⟨268,by decide⟩]

def ntree11LRRRRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11LRRRRRRLL i else ntree11LRRRRRRLR (i - 7)

def ntree11LRRRRRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1591,by decide⟩,⟨1382,by decide⟩,⟨1382,by decide⟩] | 1 => ![⟨1592,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1592,by decide⟩,⟨270,by decide⟩,⟨270,by decide⟩] | 3 => ![⟨1593,by decide⟩,⟨1384,by decide⟩,⟨1384,by decide⟩] | 4 => ![⟨1594,by decide⟩,⟨1559,by decide⟩,⟨47,by decide⟩] | 5 => ![⟨1592,by decide⟩,⟨1418,by decide⟩,⟨1193,by decide⟩] | 6 => ![⟨1595,by decide⟩,⟨1393,by decide⟩,⟨1393,by decide⟩] | _ => ![⟨226,by decide⟩,⟨1414,by decide⟩,⟨10,by decide⟩]

def ntree11LRRRRRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨223,by decide⟩,⟨1596,by decide⟩,⟨47,by decide⟩] | 1 => ![⟨174,by decide⟩,⟨174,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1597,by decide⟩,⟨1569,by decide⟩,⟨1425,by decide⟩] | 3 => ![⟨1598,by decide⟩,⟨1587,by decide⟩,⟨1426,by decide⟩] | 4 => ![⟨1599,by decide⟩,⟨163,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1444,by decide⟩,⟨1600,by decide⟩,⟨1444,by decide⟩] | 6 => ![⟨1601,by decide⟩,⟨1600,by decide⟩,⟨1601,by decide⟩] | _ => ![⟨1558,by decide⟩,⟨1602,by decide⟩,⟨1602,by decide⟩]

def ntree11LRRRRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11LRRRRRRRL i else ntree11LRRRRRRRR (i - 8)

def ntree11LRRRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11LRRRRRRL i else ntree11LRRRRRRR (i - 15)

def ntree11LRRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11LRRRRRL i else ntree11LRRRRRR (i - 31)

def ntree11LRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11LRRRRL i else ntree11LRRRRR (i - 62)

def ntree11LRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 124 then ntree11LRRRL i else ntree11LRRRR (i - 124)

def ntree11LRR (i : Nat) : Fin 3 → Fin 3109 := if i < 247 then ntree11LRRL i else ntree11LRRR (i - 247)

def ntree11LR (i : Nat) : Fin 3 → Fin 3109 := if i < 495 then ntree11LRL i else ntree11LRR (i - 495)

def ntree11L (i : Nat) : Fin 3 → Fin 3109 := if i < 989 then ntree11LL i else ntree11LR (i - 989)

def ntree11RLLLLLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1603,by decide⟩,⟨1444,by decide⟩,⟨1444,by decide⟩] | 1 => ![⟨1495,by decide⟩,⟨1602,by decide⟩,⟨1602,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨1602,by decide⟩,⟨1602,by decide⟩] | 3 => ![⟨1557,by decide⟩,⟨1604,by decide⟩,⟨1604,by decide⟩] | 4 => ![⟨1603,by decide⟩,⟨1605,by decide⟩,⟨1605,by decide⟩] | 5 => ![⟨1496,by decide⟩,⟨1606,by decide⟩,⟨1606,by decide⟩] | _ => ![⟨1493,by decide⟩,⟨1602,by decide⟩,⟨1602,by decide⟩]

def ntree11RLLLLLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1559,by decide⟩,⟨1607,by decide⟩,⟨1602,by decide⟩] | 1 => ![⟨1559,by decide⟩,⟨1559,by decide⟩,⟨1608,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1608,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1608,by decide⟩] | 4 => ![⟨1313,by decide⟩,⟨1606,by decide⟩,⟨1606,by decide⟩] | 5 => ![⟨1317,by decide⟩,⟨1602,by decide⟩,⟨1609,by decide⟩] | 6 => ![⟨1313,by decide⟩,⟨1313,by decide⟩,⟨1610,by decide⟩] | _ => ![⟨1514,by decide⟩,⟨1514,by decide⟩,⟨315,by decide⟩]

def ntree11RLLLLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLLLLLLLL i else ntree11RLLLLLLLR (i - 7)

def ntree11RLLLLLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨1398,by decide⟩,⟨315,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨318,by decide⟩,⟨318,by decide⟩] | 2 => ![⟨174,by decide⟩,⟨174,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1611,by decide⟩,⟨174,by decide⟩,⟨1317,by decide⟩] | 4 => ![⟨1460,by decide⟩,⟨1602,by decide⟩,⟨1612,by decide⟩] | 5 => ![⟨1613,by decide⟩,⟨1514,by decide⟩,⟨1460,by decide⟩] | _ => ![⟨1613,by decide⟩,⟨1614,by decide⟩,⟨1612,by decide⟩]

def ntree11RLLLLLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1615,by decide⟩,⟨174,by decide⟩,⟨1460,by decide⟩] | 1 => ![⟨1615,by decide⟩,⟨250,by decide⟩,⟨1460,by decide⟩] | 2 => ![⟨1495,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1514,by decide⟩,⟨1614,by decide⟩,⟨1602,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨1602,by decide⟩,⟨1602,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨96,by decide⟩,⟨1608,by decide⟩] | 6 => ![⟨1384,by decide⟩,⟨1616,by decide⟩,⟨1616,by decide⟩] | _ => ![⟨10,by decide⟩,⟨318,by decide⟩,⟨318,by decide⟩]

def ntree11RLLLLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLLLLLLRL i else ntree11RLLLLLLRR (i - 7)

def ntree11RLLLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLLLLLLL i else ntree11RLLLLLLR (i - 15)

def ntree11RLLLLLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1558,by decide⟩,⟨10,by decide⟩,⟨315,by decide⟩] | 1 => ![⟨1617,by decide⟩,⟨1514,by decide⟩,⟨135,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨1618,by decide⟩,⟨1618,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨1618,by decide⟩,⟨1618,by decide⟩] | 4 => ![⟨1558,by decide⟩,⟨1494,by decide⟩,⟨1494,by decide⟩] | 5 => ![⟨1527,by decide⟩,⟨1618,by decide⟩,⟨1618,by decide⟩] | _ => ![⟨1528,by decide⟩,⟨1619,by decide⟩,⟨1619,by decide⟩]

def ntree11RLLLLLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨47,by decide⟩,⟨1618,by decide⟩,⟨1620,by decide⟩] | 1 => ![⟨1621,by decide⟩,⟨332,by decide⟩,⟨1338,by decide⟩] | 2 => ![⟨1338,by decide⟩,⟨270,by decide⟩,⟨1622,by decide⟩] | 3 => ![⟨1340,by decide⟩,⟨1619,by decide⟩,⟨1623,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨1624,by decide⟩,⟨318,by decide⟩] | 5 => ![⟨47,by decide⟩,⟨1624,by decide⟩,⟨336,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1625,by decide⟩] | _ => ![⟨1338,by decide⟩,⟨318,by decide⟩,⟨1626,by decide⟩]

def ntree11RLLLLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLLLLLRLL i else ntree11RLLLLLRLR (i - 7)

def ntree11RLLLLLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1627,by decide⟩,⟨341,by decide⟩,⟨1626,by decide⟩] | 1 => ![⟨1460,by decide⟩,⟨1618,by decide⟩,⟨1628,by decide⟩] | 2 => ![⟨1460,by decide⟩,⟨1629,by decide⟩,⟨1628,by decide⟩] | 3 => ![⟨1460,by decide⟩,⟨270,by decide⟩,⟨1630,by decide⟩] | 4 => ![⟨1631,by decide⟩,⟨206,by decide⟩,⟨1460,by decide⟩] | 5 => ![⟨1631,by decide⟩,⟨283,by decide⟩,⟨1630,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1608,by decide⟩] | _ => ![⟨47,by decide⟩,⟨1629,by decide⟩,⟨1620,by decide⟩]

def ntree11RLLLLLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨206,by decide⟩,⟨206,by decide⟩,⟨1608,by decide⟩] | 1 => ![⟨1627,by decide⟩,⟨283,by decide⟩,⟨1622,by decide⟩] | 2 => ![⟨1632,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨343,by decide⟩] | 6 => ![⟨1558,by decide⟩,⟨212,by decide⟩,⟨212,by decide⟩] | _ => ![⟨1633,by decide⟩,⟨1444,by decide⟩,⟨1444,by decide⟩]

def ntree11RLLLLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLLLLLRRL i else ntree11RLLLLLRRR (i - 8)

def ntree11RLLLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLLLLLRL i else ntree11RLLLLLRR (i - 15)

def ntree11RLLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 30 then ntree11RLLLLLL i else ntree11RLLLLLR (i - 30)

def ntree11RLLLLRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1592,by decide⟩,⟨1618,by decide⟩,⟨1618,by decide⟩] | 1 => ![⟨1592,by decide⟩,⟨1544,by decide⟩,⟨1544,by decide⟩] | 2 => ![⟨1633,by decide⟩,⟨1634,by decide⟩,⟨1634,by decide⟩] | 3 => ![⟨1593,by decide⟩,⟨1635,by decide⟩,⟨1635,by decide⟩] | 4 => ![⟨1594,by decide⟩,⟨1636,by decide⟩,⟨1620,by decide⟩] | 5 => ![⟨1592,by decide⟩,⟨10,by decide⟩,⟨1608,by decide⟩] | _ => ![⟨1637,by decide⟩,⟨270,by decide⟩,⟨1622,by decide⟩]

def ntree11RLLLLRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1514,by decide⟩,⟨1638,by decide⟩,⟨350,by decide⟩] | 1 => ![⟨1549,by decide⟩,⟨1638,by decide⟩,⟨351,by decide⟩] | 2 => ![⟨1338,by decide⟩,⟨350,by decide⟩,⟨1639,by decide⟩] | 3 => ![⟨1550,by decide⟩,⟨353,by decide⟩,⟨1639,by decide⟩] | 4 => ![⟨1384,by decide⟩,⟨1640,by decide⟩,⟨1640,by decide⟩] | 5 => ![⟨1641,by decide⟩,⟨350,by decide⟩,⟨350,by decide⟩] | 6 => ![⟨1554,by decide⟩,⟨350,by decide⟩,⟨350,by decide⟩] | _ => ![⟨1642,by decide⟩,⟨350,by decide⟩,⟨350,by decide⟩]

def ntree11RLLLLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLLLLRLLL i else ntree11RLLLLRLLR (i - 7)

def ntree11RLLLLRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1592,by decide⟩,⟨1643,by decide⟩,⟨315,by decide⟩] | 1 => ![⟨1644,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 2 => ![⟨1645,by decide⟩,⟨15,by decide⟩,⟨1329,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨1331,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1646,by decide⟩,⟨14,by decide⟩,⟨1647,by decide⟩] | 6 => ![⟨1493,by decide⟩,⟨10,by decide⟩,⟨1331,by decide⟩] | _ => ![⟨1497,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩]

def ntree11RLLLLRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨1648,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1644,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1645,by decide⟩,⟨14,by decide⟩,⟨1330,by decide⟩] | 4 => ![⟨1649,by decide⟩,⟨365,by decide⟩,⟨1650,by decide⟩] | 5 => ![⟨1514,by decide⟩,⟨1651,by decide⟩,⟨11,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨1652,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1522,by decide⟩,⟨379,by decide⟩,⟨1329,by decide⟩]

def ntree11RLLLLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLLLLRLRL i else ntree11RLLLLRLRR (i - 8)

def ntree11RLLLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLLLLRLL i else ntree11RLLLLRLR (i - 15)

def ntree11RLLLLRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨384,by decide⟩,⟨1331,by decide⟩] | 1 => ![⟨1510,by decide⟩,⟨386,by decide⟩,⟨1333,by decide⟩] | 2 => ![⟨1513,by decide⟩,⟨1651,by decide⟩,⟨1334,by decide⟩] | 3 => ![⟨1322,by decide⟩,⟨1652,by decide⟩,⟨1322,by decide⟩] | 4 => ![⟨1653,by decide⟩,⟨14,by decide⟩,⟨1354,by decide⟩] | 5 => ![⟨1654,by decide⟩,⟨10,by decide⟩,⟨1654,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1655,by decide⟩]

def ntree11RLLLLRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1656,by decide⟩,⟨14,by decide⟩,⟨1654,by decide⟩] | 1 => ![⟨1654,by decide⟩,⟨1494,by decide⟩,⟨1657,by decide⟩] | 2 => ![⟨1658,by decide⟩,⟨391,by decide⟩,⟨1658,by decide⟩] | 3 => ![⟨1659,by decide⟩,⟨393,by decide⟩,⟨1658,by decide⟩] | 4 => ![⟨1354,by decide⟩,⟨10,by decide⟩,⟨1354,by decide⟩] | 5 => ![⟨1653,by decide⟩,⟨14,by decide⟩,⟨1372,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨1660,by decide⟩,⟨10,by decide⟩] | _ => ![⟨10,by decide⟩,⟨1661,by decide⟩,⟨10,by decide⟩]

def ntree11RLLLLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLLLLRRLL i else ntree11RLLLLRRLR (i - 7)

def ntree11RLLLLRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1527,by decide⟩,⟨419,by decide⟩,⟨1331,by decide⟩] | 1 => ![⟨1654,by decide⟩,⟨1662,by decide⟩,⟨1654,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨1662,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨1663,by decide⟩,⟨1544,by decide⟩] | 4 => ![⟨1656,by decide⟩,⟨1663,by decide⟩,⟨1664,by decide⟩] | 5 => ![⟨1527,by decide⟩,⟨1662,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨47,by decide⟩,⟨1665,by decide⟩,⟨47,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11RLLLLRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1666,by decide⟩,⟨163,by decide⟩,⟨1654,by decide⟩] | 1 => ![⟨163,by decide⟩,⟨163,by decide⟩,⟨1331,by decide⟩] | 2 => ![⟨1514,by decide⟩,⟨1667,by decide⟩,⟨1374,by decide⟩] | 3 => ![⟨163,by decide⟩,⟨418,by decide⟩,⟨65,by decide⟩] | 4 => ![⟨163,by decide⟩,⟨1668,by decide⟩,⟨1374,by decide⟩] | 5 => ![⟨1514,by decide⟩,⟨1514,by decide⟩,⟨1378,by decide⟩] | 6 => ![⟨1549,by decide⟩,⟨1669,by decide⟩,⟨1377,by decide⟩] | _ => ![⟨1554,by decide⟩,⟨420,by decide⟩,⟨1378,by decide⟩]

def ntree11RLLLLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLLLLRRRL i else ntree11RLLLLRRRR (i - 8)

def ntree11RLLLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLLLLRRL i else ntree11RLLLLRRR (i - 15)

def ntree11RLLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RLLLLRL i else ntree11RLLLLRR (i - 31)

def ntree11RLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 61 then ntree11RLLLLL i else ntree11RLLLLR (i - 61)

def ntree11RLLLRLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1670,by decide⟩,⟨1671,by decide⟩,⟨1671,by decide⟩] | 1 => ![⟨1670,by decide⟩,⟨1670,by decide⟩,⟨1670,by decide⟩] | 2 => ![⟨1672,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨1673,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1674,by decide⟩,⟨1670,by decide⟩,⟨1670,by decide⟩] | 5 => ![⟨1672,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1675,by decide⟩,⟨1389,by decide⟩,⟨426,by decide⟩]

def ntree11RLLLRLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨1676,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨1677,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨163,by decide⟩,⟨1678,by decide⟩,⟨1679,by decide⟩] | 5 => ![⟨1644,by decide⟩,⟨1677,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨1322,by decide⟩,⟨1673,by decide⟩,⟨1322,by decide⟩] | _ => ![⟨1322,by decide⟩,⟨1680,by decide⟩,⟨1322,by decide⟩]

def ntree11RLLLRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLLLRLLLL i else ntree11RLLLRLLLR (i - 7)

def ntree11RLLLRLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1681,by decide⟩,⟨379,by decide⟩,⟨11,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨384,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1682,by decide⟩,⟨1683,by decide⟩,⟨1684,by decide⟩] | 3 => ![⟨1685,by decide⟩,⟨1389,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1685,by decide⟩,⟨1686,by decide⟩,⟨1563,by decide⟩] | 5 => ![⟨1687,by decide⟩,⟨1688,by decide⟩,⟨1689,by decide⟩] | 6 => ![⟨1690,by decide⟩,⟨1691,by decide⟩,⟨1692,by decide⟩] | _ => ![⟨1693,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11RLLLRLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1672,by decide⟩,⟨1694,by decide⟩,⟨51,by decide⟩] | 1 => ![⟨1695,by decide⟩,⟨1411,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨1694,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨47,by decide⟩,⟨1677,by decide⟩,⟨47,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨1696,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨201,by decide⟩,⟨1697,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨1693,by decide⟩,⟨1677,by decide⟩,⟨1579,by decide⟩] | _ => ![⟨1322,by decide⟩,⟨1694,by decide⟩,⟨1322,by decide⟩]

def ntree11RLLLRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLLLRLLRL i else ntree11RLLLRLLRR (i - 8)

def ntree11RLLLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLLLRLLL i else ntree11RLLLRLLR (i - 15)

def ntree11RLLLRLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1698,by decide⟩,⟨11,by decide⟩,⟨1699,by decide⟩] | 1 => ![⟨1700,by decide⟩,⟨1701,by decide⟩,⟨1702,by decide⟩] | 2 => ![⟨1703,by decide⟩,⟨1704,by decide⟩,⟨1705,by decide⟩] | 3 => ![⟨1706,by decide⟩,⟨449,by decide⟩,⟨1707,by decide⟩] | 4 => ![⟨1708,by decide⟩,⟨1709,by decide⟩,⟨1710,by decide⟩] | 5 => ![⟨1693,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1711,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11RLLLRLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1712,by decide⟩,⟨1389,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨1711,by decide⟩,⟨1694,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1711,by decide⟩,⟨270,by decide⟩,⟨270,by decide⟩] | 3 => ![⟨1713,by decide⟩,⟨1670,by decide⟩,⟨1670,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨1662,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1389,by decide⟩,⟨1714,by decide⟩,⟨270,by decide⟩] | 6 => ![⟨1715,by decide⟩,⟨1714,by decide⟩,⟨270,by decide⟩] | _ => ![⟨1716,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11RLLLRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLLLRLRLL i else ntree11RLLLRLRLR (i - 7)

def ntree11RLLLRLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨1717,by decide⟩,⟨10,by decide⟩,⟨1718,by decide⟩] | 2 => ![⟨1719,by decide⟩,⟨163,by decide⟩,⟨1718,by decide⟩] | 3 => ![⟨1720,by decide⟩,⟨1389,by decide⟩,⟨1718,by decide⟩] | 4 => ![⟨1721,by decide⟩,⟨1722,by decide⟩,⟨1723,by decide⟩] | 5 => ![⟨118,by decide⟩,⟨1662,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨462,by decide⟩,⟨1724,by decide⟩,⟨1374,by decide⟩] | _ => ![⟨1725,by decide⟩,⟨1726,by decide⟩,⟨1727,by decide⟩]

def ntree11RLLLRLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1728,by decide⟩,⟨270,by decide⟩,⟨1729,by decide⟩] | 1 => ![⟨1730,by decide⟩,⟨1731,by decide⟩,⟨1732,by decide⟩] | 2 => ![⟨1444,by decide⟩,⟨1605,by decide⟩,⟨1605,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨1677,by decide⟩,⟨315,by decide⟩] | 4 => ![⟨1514,by decide⟩,⟨1733,by decide⟩,⟨1457,by decide⟩] | 5 => ![⟨14,by decide⟩,⟨1734,by decide⟩,⟨318,by decide⟩] | 6 => ![⟨1735,by decide⟩,⟨1651,by decide⟩,⟨470,by decide⟩] | _ => ![⟨1736,by decide⟩,⟨1388,by decide⟩,⟨470,by decide⟩]

def ntree11RLLLRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLLLRLRRL i else ntree11RLLLRLRRR (i - 8)

def ntree11RLLLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLLLRLRL i else ntree11RLLLRLRR (i - 15)

def ntree11RLLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RLLLRLL i else ntree11RLLLRLR (i - 31)

def ntree11RLLLRRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1389,by decide⟩,⟨1737,by decide⟩,⟨318,by decide⟩] | 1 => ![⟨1736,by decide⟩,⟨1737,by decide⟩,⟨474,by decide⟩] | 2 => ![⟨1389,by decide⟩,⟨1389,by decide⟩,⟨315,by decide⟩] | 3 => ![⟨1493,by decide⟩,⟨40,by decide⟩,⟨40,by decide⟩] | 4 => ![⟨1466,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11RLLLRRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1411,by decide⟩,⟨1738,by decide⟩,⟨1494,by decide⟩] | 1 => ![⟨49,by decide⟩,⟨1734,by decide⟩,⟨336,by decide⟩] | 2 => ![⟨14,by decide⟩,⟨1739,by decide⟩,⟨1740,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨343,by decide⟩] | 5 => ![⟨1444,by decide⟩,⟨1741,by decide⟩,⟨1444,by decide⟩] | 6 => ![⟨1446,by decide⟩,⟨1742,by decide⟩,⟨1634,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1743,by decide⟩]

def ntree11RLLLRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLLLRRLLL i else ntree11RLLLRRLLR (i - 7)

def ntree11RLLLRRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1389,by decide⟩,⟨1744,by decide⟩,⟨350,by decide⟩] | 1 => ![⟨1427,by decide⟩,⟨1744,by decide⟩,⟨351,by decide⟩] | 2 => ![⟨1437,by decide⟩,⟨350,by decide⟩,⟨350,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨1745,by decide⟩,⟨1745,by decide⟩] | 4 => ![⟨1746,by decide⟩,⟨0,by decide⟩,⟨1746,by decide⟩] | 5 => ![⟨1747,by decide⟩,⟨2,by decide⟩,⟨1746,by decide⟩] | 6 => ![⟨1748,by decide⟩,⟨502,by decide⟩,⟨1748,by decide⟩] | _ => ![⟨1748,by decide⟩,⟨10,by decide⟩,⟨1748,by decide⟩]

def ntree11RLLLRRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1749,by decide⟩,⟨505,by decide⟩,⟨1750,by decide⟩] | 1 => ![⟨1748,by decide⟩,⟨506,by decide⟩,⟨1750,by decide⟩] | 2 => ![⟨1749,by decide⟩,⟨14,by decide⟩,⟨1748,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1751,by decide⟩] | 4 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨1751,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1752,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨502,by decide⟩,⟨1751,by decide⟩] | _ => ![⟨1748,by decide⟩,⟨1745,by decide⟩,⟨1753,by decide⟩]

def ntree11RLLLRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLLLRRLRL i else ntree11RLLLRRLRR (i - 8)

def ntree11RLLLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLLLRRLL i else ntree11RLLLRRLR (i - 15)

def ntree11RLLLRRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1754,by decide⟩,⟨512,by decide⟩,⟨1754,by decide⟩] | 1 => ![⟨1755,by decide⟩,⟨513,by decide⟩,⟨1754,by decide⟩] | 2 => ![⟨1756,by decide⟩,⟨514,by decide⟩,⟨1756,by decide⟩] | 3 => ![⟨1757,by decide⟩,⟨515,by decide⟩,⟨1756,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨1758,by decide⟩,⟨1758,by decide⟩] | 5 => ![⟨30,by decide⟩,⟨1759,by decide⟩,⟨1758,by decide⟩] | _ => ![⟨10,by decide⟩,⟨1758,by decide⟩,⟨1760,by decide⟩]

def ntree11RLLLRRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨514,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨1761,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1762,by decide⟩,⟨520,by decide⟩,⟨1756,by decide⟩] | 4 => ![⟨1322,by decide⟩,⟨502,by decide⟩,⟨1322,by decide⟩] | 5 => ![⟨1756,by decide⟩,⟨525,by decide⟩,⟨1756,by decide⟩] | 6 => ![⟨1322,by decide⟩,⟨1761,by decide⟩,⟨1322,by decide⟩] | _ => ![⟨47,by decide⟩,⟨1745,by decide⟩,⟨1763,by decide⟩]

def ntree11RLLLRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLLLRRRLL i else ntree11RLLLRRRLR (i - 7)

def ntree11RLLLRRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨502,by decide⟩,⟨1344,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨1764,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨30,by decide⟩,⟨1765,by decide⟩,⟨1766,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨1766,by decide⟩,⟨1766,by decide⟩] | 4 => ![⟨47,by decide⟩,⟨1764,by decide⟩,⟨47,by decide⟩] | 5 => ![⟨1322,by decide⟩,⟨1764,by decide⟩,⟨1322,by decide⟩] | 6 => ![⟨1346,by decide⟩,⟨1767,by decide⟩,⟨1346,by decide⟩] | _ => ![⟨10,by decide⟩,⟨549,by decide⟩,⟨549,by decide⟩]

def ntree11RLLLRRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨14,by decide⟩,⟨551,by decide⟩,⟨1768,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨549,by decide⟩,⟨1768,by decide⟩] | 2 => ![⟨47,by decide⟩,⟨549,by decide⟩,⟨1769,by decide⟩] | 3 => ![⟨49,by decide⟩,⟨551,by decide⟩,⟨1769,by decide⟩] | 4 => ![⟨47,by decide⟩,⟨1770,by decide⟩,⟨1771,by decide⟩] | 5 => ![⟨560,by decide⟩,⟨1766,by decide⟩,⟨1772,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨569,by decide⟩,⟨10,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11RLLLRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLLLRRRRL i else ntree11RLLLRRRRR (i - 8)

def ntree11RLLLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLLLRRRL i else ntree11RLLLRRRR (i - 15)

def ntree11RLLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RLLLRRL i else ntree11RLLLRRR (i - 31)

def ntree11RLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11RLLLRL i else ntree11RLLLRR (i - 62)

def ntree11RLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 123 then ntree11RLLLL i else ntree11RLLLR (i - 123)

def ntree11RLLRLLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨47,by decide⟩,⟨569,by decide⟩,⟨47,by decide⟩] | 1 => ![⟨1379,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1773,by decide⟩,⟨1773,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨1774,by decide⟩,⟨1774,by decide⟩] | 4 => ![⟨1386,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1775,by decide⟩,⟨1380,by decide⟩,⟨574,by decide⟩] | _ => ![⟨574,by decide⟩,⟨0,by decide⟩,⟨574,by decide⟩]

def ntree11RLLRLLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨578,by decide⟩,⟨10,by decide⟩,⟨578,by decide⟩] | 1 => ![⟨1776,by decide⟩,⟨1777,by decide⟩,⟨580,by decide⟩] | 2 => ![⟨1389,by decide⟩,⟨1777,by decide⟩,⟨506,by decide⟩] | 3 => ![⟨1390,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1778,by decide⟩,⟨1391,by decide⟩,⟨581,by decide⟩] | 5 => ![⟨581,by decide⟩,⟨1779,by decide⟩,⟨1780,by decide⟩] | 6 => ![⟨581,by decide⟩,⟨10,by decide⟩,⟨581,by decide⟩] | _ => ![⟨1390,by decide⟩,⟨10,by decide⟩,⟨1751,by decide⟩]

def ntree11RLLRLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLLRLLLLL i else ntree11RLLRLLLLR (i - 7)

def ntree11RLLRLLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1781,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1782,by decide⟩,⟨1782,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨1783,by decide⟩,⟨1783,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨1784,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1785,by decide⟩,⟨590,by decide⟩,⟨1320,by decide⟩] | 5 => ![⟨1786,by decide⟩,⟨594,by decide⟩,⟨1322,by decide⟩] | 6 => ![⟨1322,by decide⟩,⟨1787,by decide⟩,⟨1788,by decide⟩] | _ => ![⟨1789,by decide⟩,⟨1789,by decide⟩,⟨1789,by decide⟩]

def ntree11RLLRLLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1790,by decide⟩,⟨10,by decide⟩,⟨1790,by decide⟩] | 1 => ![⟨1791,by decide⟩,⟨1791,by decide⟩,⟨1789,by decide⟩] | 2 => ![⟨1789,by decide⟩,⟨1792,by decide⟩,⟨1792,by decide⟩] | 3 => ![⟨1789,by decide⟩,⟨1789,by decide⟩,⟨1789,by decide⟩] | 4 => ![⟨1386,by decide⟩,⟨1758,by decide⟩,⟨1758,by decide⟩] | 5 => ![⟨1793,by decide⟩,⟨1789,by decide⟩,⟨1793,by decide⟩] | 6 => ![⟨1794,by decide⟩,⟨1791,by decide⟩,⟨1793,by decide⟩] | _ => ![⟨1793,by decide⟩,⟨1795,by decide⟩,⟨1793,by decide⟩]

def ntree11RLLRLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLLRLLLRL i else ntree11RLLRLLLRR (i - 8)

def ntree11RLLRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLLRLLLL i else ntree11RLLRLLLR (i - 15)

def ntree11RLLRLLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1796,by decide⟩,⟨584,by decide⟩,⟨1796,by decide⟩] | 1 => ![⟨1408,by decide⟩,⟨1406,by decide⟩,⟨44,by decide⟩] | 2 => ![⟨1413,by decide⟩,⟨1411,by decide⟩,⟨47,by decide⟩] | 3 => ![⟨1797,by decide⟩,⟨1406,by decide⟩,⟨574,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨1798,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨1799,by decide⟩,⟨1411,by decide⟩,⟨578,by decide⟩] | _ => ![⟨10,by decide⟩,⟨1800,by decide⟩,⟨10,by decide⟩]

def ntree11RLLRLLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1801,by decide⟩,⟨1415,by decide⟩,⟨581,by decide⟩] | 1 => ![⟨1417,by decide⟩,⟨1415,by decide⟩,⟨47,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨1802,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨47,by decide⟩,⟨1803,by decide⟩,⟨47,by decide⟩] | 6 => ![⟨1320,by decide⟩,⟨1798,by decide⟩,⟨1320,by decide⟩] | _ => ![⟨1322,by decide⟩,⟨1800,by decide⟩,⟨1322,by decide⟩]

def ntree11RLLRLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLLRLLRLL i else ntree11RLLRLLRLR (i - 7)

def ntree11RLLRLLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1322,by decide⟩,⟨1802,by decide⟩,⟨1322,by decide⟩] | 1 => ![⟨1804,by decide⟩,⟨1789,by decide⟩,⟨1804,by decide⟩] | 2 => ![⟨1805,by decide⟩,⟨1805,by decide⟩,⟨1789,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1789,by decide⟩,⟨1806,by decide⟩,⟨1806,by decide⟩] | 5 => ![⟨1807,by decide⟩,⟨1805,by decide⟩,⟨1793,by decide⟩] | 6 => ![⟨1808,by decide⟩,⟨1809,by decide⟩,⟨1808,by decide⟩] | _ => ![⟨1810,by decide⟩,⟨1380,by decide⟩,⟨625,by decide⟩]

def ntree11RLLRLLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨625,by decide⟩,⟨1798,by decide⟩,⟨625,by decide⟩] | 1 => ![⟨1811,by decide⟩,⟨1812,by decide⟩,⟨631,by decide⟩] | 2 => ![⟨1389,by decide⟩,⟨1812,by decide⟩,⟨549,by decide⟩] | 3 => ![⟨1813,by decide⟩,⟨1391,by decide⟩,⟨635,by decide⟩] | 4 => ![⟨635,by decide⟩,⟨10,by decide⟩,⟨1814,by decide⟩] | 5 => ![⟨635,by decide⟩,⟨1802,by decide⟩,⟨635,by decide⟩] | 6 => ![⟨1432,by decide⟩,⟨1802,by decide⟩,⟨1751,by decide⟩] | _ => ![⟨10,by decide⟩,⟨1815,by decide⟩,⟨1815,by decide⟩]

def ntree11RLLRLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLLRLLRRL i else ntree11RLLRLLRRR (i - 8)

def ntree11RLLRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLLRLLRL i else ntree11RLLRLLRR (i - 15)

def ntree11RLLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RLLRLLL i else ntree11RLLRLLR (i - 31)

def ntree11RLLRLRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨1816,by decide⟩,⟨1815,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1817,by decide⟩] | 2 => ![⟨1437,by decide⟩,⟨1766,by decide⟩,⟨1766,by decide⟩] | 3 => ![⟨1818,by decide⟩,⟨1789,by decide⟩,⟨1789,by decide⟩] | 4 => ![⟨1819,by decide⟩,⟨1389,by decide⟩,⟨635,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨1820,by decide⟩,⟨1443,by decide⟩] | _ => ![⟨1386,by decide⟩,⟨1745,by decide⟩,⟨1745,by decide⟩]

def ntree11RLLRLRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1821,by decide⟩,⟨1444,by decide⟩,⟨1821,by decide⟩] | 1 => ![⟨1822,by decide⟩,⟨10,by decide⟩,⟨1822,by decide⟩] | 2 => ![⟨1823,by decide⟩,⟨1446,by decide⟩,⟨1821,by decide⟩] | 3 => ![⟨1824,by decide⟩,⟨1389,by decide⟩,⟨1822,by decide⟩] | 4 => ![⟨642,by decide⟩,⟨14,by decide⟩,⟨1825,by decide⟩] | 5 => ![⟨644,by decide⟩,⟨10,by decide⟩,⟨1318,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨1783,by decide⟩,⟨1783,by decide⟩] | _ => ![⟨1826,by decide⟩,⟨514,by decide⟩,⟨1826,by decide⟩]

def ntree11RLLRLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLLRLRLLL i else ntree11RLLRLRLLR (i - 7)

def ntree11RLLRLRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1827,by decide⟩,⟨515,by decide⟩,⟨1826,by decide⟩] | 1 => ![⟨1828,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1829,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩] | 3 => ![⟨1830,by decide⟩,⟨1389,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1831,by decide⟩,⟨1831,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1832,by decide⟩,⟨1832,by decide⟩,⟨514,by decide⟩] | 6 => ![⟨1831,by decide⟩,⟨1831,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1828,by decide⟩,⟨1774,by decide⟩,⟨1774,by decide⟩]

def ntree11RLLRLRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1828,by decide⟩,⟨1761,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨1831,by decide⟩,⟨1831,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1832,by decide⟩,⟨1832,by decide⟩,⟨514,by decide⟩] | 3 => ![⟨1833,by decide⟩,⟨1831,by decide⟩,⟨581,by decide⟩] | 4 => ![⟨1834,by decide⟩,⟨1832,by decide⟩,⟨655,by decide⟩] | 5 => ![⟨1833,by decide⟩,⟨1835,by decide⟩,⟨656,by decide⟩] | 6 => ![⟨1831,by decide⟩,⟨1835,by decide⟩,⟨40,by decide⟩] | _ => ![⟨1386,by decide⟩,⟨10,by decide⟩,⟨1344,by decide⟩]

def ntree11RLLRLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLLRLRLRL i else ntree11RLLRLRLRR (i - 8)

def ntree11RLLRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLLRLRLL i else ntree11RLLRLRLR (i - 15)

def ntree11RLLRLRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1413,by decide⟩,⟨1836,by decide⟩,⟨1763,by decide⟩] | 1 => ![⟨1837,by decide⟩,⟨1411,by decide⟩,⟨581,by decide⟩] | 2 => ![⟨581,by decide⟩,⟨1838,by decide⟩,⟨1839,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨1840,by decide⟩,⟨1841,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1842,by decide⟩] | 5 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨1843,by decide⟩] | _ => ![⟨1460,by decide⟩,⟨1838,by decide⟩,⟨1844,by decide⟩]

def ntree11RLLRLRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1461,by decide⟩,⟨1840,by decide⟩,⟨1845,by decide⟩] | 1 => ![⟨1460,by decide⟩,⟨1802,by decide⟩,⟨1460,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨1838,by decide⟩,⟨1846,by decide⟩] | 3 => ![⟨1847,by decide⟩,⟨1831,by decide⟩,⟨47,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1848,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨1831,by decide⟩,⟨1849,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1411,by decide⟩,⟨1411,by decide⟩,⟨673,by decide⟩]

def ntree11RLLRLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLLRLRRLL i else ntree11RLLRLRRLR (i - 7)

def ntree11RLLRLRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1847,by decide⟩,⟨1849,by decide⟩,⟨47,by decide⟩] | 1 => ![⟨581,by decide⟩,⟨65,by decide⟩,⟨672,by decide⟩] | 2 => ![⟨1463,by decide⟩,⟨1802,by decide⟩,⟨668,by decide⟩] | 3 => ![⟨581,by decide⟩,⟨1764,by decide⟩,⟨581,by decide⟩] | 4 => ![⟨1850,by decide⟩,⟨1444,by decide⟩,⟨1444,by decide⟩] | 5 => ![⟨1851,by decide⟩,⟨1446,by decide⟩,⟨1852,by decide⟩] | 6 => ![⟨1853,by decide⟩,⟨1389,by decide⟩,⟨10,by decide⟩] | _ => ![⟨675,by decide⟩,⟨1838,by decide⟩,⟨1854,by decide⟩]

def ntree11RLLRLRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨676,by decide⟩,⟨1840,by decide⟩,⟨1855,by decide⟩] | 1 => ![⟨675,by decide⟩,⟨1802,by decide⟩,⟨1318,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1817,by decide⟩] | 3 => ![⟨1856,by decide⟩,⟨1832,by decide⟩,⟨556,by decide⟩] | 4 => ![⟨1857,by decide⟩,⟨1831,by decide⟩,⟨560,by decide⟩] | 5 => ![⟨1858,by decide⟩,⟨1858,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1858,by decide⟩,⟨1858,by decide⟩,⟨683,by decide⟩] | _ => ![⟨1859,by decide⟩,⟨1859,by decide⟩,⟨10,by decide⟩]

def ntree11RLLRLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLLRLRRRL i else ntree11RLLRLRRRR (i - 8)

def ntree11RLLRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLLRLRRL i else ntree11RLLRLRRR (i - 15)

def ntree11RLLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RLLRLRL i else ntree11RLLRLRR (i - 31)

def ntree11RLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11RLLRLL i else ntree11RLLRLR (i - 62)

def ntree11RLLRRLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1859,by decide⟩,⟨1859,by decide⟩,⟨684,by decide⟩] | 1 => ![⟨1860,by decide⟩,⟨1858,by decide⟩,⟨1746,by decide⟩] | 2 => ![⟨1859,by decide⟩,⟨1861,by decide⟩,⟨1494,by decide⟩] | 3 => ![⟨1862,by decide⟩,⟨1861,by decide⟩,⟨1863,by decide⟩] | 4 => ![⟨1862,by decide⟩,⟨1859,by decide⟩,⟨1748,by decide⟩] | 5 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1865,by decide⟩,⟨1864,by decide⟩,⟨1748,by decide⟩]

def ntree11RLLRRLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨691,by decide⟩] | 1 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨1500,by decide⟩] | 2 => ![⟨1866,by decide⟩,⟨1866,by decide⟩,⟨512,by decide⟩] | 3 => ![⟨1867,by decide⟩,⟨1867,by decide⟩,⟨514,by decide⟩] | 4 => ![⟨1868,by decide⟩,⟨1858,by decide⟩,⟨1320,by decide⟩] | 5 => ![⟨1869,by decide⟩,⟨1866,by decide⟩,⟨1754,by decide⟩] | 6 => ![⟨1870,by decide⟩,⟨1859,by decide⟩,⟨1322,by decide⟩] | _ => ![⟨1871,by decide⟩,⟨1867,by decide⟩,⟨1756,by decide⟩]

def ntree11RLLRRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLLRRLLLL i else ntree11RLLRRLLLR (i - 7)

def ntree11RLLRRLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1872,by decide⟩,⟨1864,by decide⟩,⟨1322,by decide⟩] | 1 => ![⟨1873,by decide⟩,⟨1874,by decide⟩,⟨1756,by decide⟩] | 2 => ![⟨1874,by decide⟩,⟨1874,by decide⟩,⟨514,by decide⟩] | 3 => ![⟨1864,by decide⟩,⟨1875,by decide⟩,⟨1521,by decide⟩] | 4 => ![⟨1872,by decide⟩,⟨1876,by decide⟩,⟨1877,by decide⟩] | 5 => ![⟨1872,by decide⟩,⟨1875,by decide⟩,⟨1525,by decide⟩] | 6 => ![⟨1878,by decide⟩,⟨1858,by decide⟩,⟨44,by decide⟩] | _ => ![⟨1879,by decide⟩,⟨1859,by decide⟩,⟨47,by decide⟩]

def ntree11RLLRRLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1880,by decide⟩,⟨1864,by decide⟩,⟨47,by decide⟩] | 1 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨1529,by decide⟩] | 2 => ![⟨1881,by decide⟩,⟨1882,by decide⟩,⟨1346,by decide⟩] | 3 => ![⟨1864,by decide⟩,⟨1883,by decide⟩,⟨212,by decide⟩] | 4 => ![⟨1322,by decide⟩,⟨1884,by decide⟩,⟨1885,by decide⟩] | 5 => ![⟨1872,by decide⟩,⟨1883,by decide⟩,⟨1543,by decide⟩] | 6 => ![⟨1859,by decide⟩,⟨1886,by decide⟩,⟨1544,by decide⟩] | _ => ![⟨1859,by decide⟩,⟨1886,by decide⟩,⟨1887,by decide⟩]

def ntree11RLLRRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLLRRLLRL i else ntree11RLLRRLLRR (i - 8)

def ntree11RLLRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLLRRLLL i else ntree11RLLRRLLR (i - 15)

def ntree11RLLRRLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1888,by decide⟩,⟨1866,by decide⟩,⟨554,by decide⟩] | 1 => ![⟨1889,by decide⟩,⟨1858,by decide⟩,⟨555,by decide⟩] | 2 => ![⟨1890,by decide⟩,⟨1867,by decide⟩,⟨556,by decide⟩] | 3 => ![⟨1891,by decide⟩,⟨1874,by decide⟩,⟨556,by decide⟩] | 4 => ![⟨1892,by decide⟩,⟨1864,by decide⟩,⟨560,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨1884,by decide⟩,⟨1884,by decide⟩] | _ => ![⟨10,by decide⟩,⟨1764,by decide⟩,⟨1500,by decide⟩]

def ntree11RLLRRLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1893,by decide⟩,⟨1858,by decide⟩,⟨574,by decide⟩] | 1 => ![⟨1893,by decide⟩,⟨1858,by decide⟩,⟨730,by decide⟩] | 2 => ![⟨1894,by decide⟩,⟨1859,by decide⟩,⟨578,by decide⟩] | 3 => ![⟨1894,by decide⟩,⟨1859,by decide⟩,⟨731,by decide⟩] | 4 => ![⟨1895,by decide⟩,⟨1864,by decide⟩,⟨581,by decide⟩] | 5 => ![⟨1896,by decide⟩,⟨1896,by decide⟩,⟨584,by decide⟩] | 6 => ![⟨1897,by decide⟩,⟨1559,by decide⟩,⟨581,by decide⟩] | _ => ![⟨1895,by decide⟩,⟨1864,by decide⟩,⟨734,by decide⟩]

def ntree11RLLRRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLLRRLRLL i else ntree11RLLRRLRLR (i - 7)

def ntree11RLLRRLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1859,by decide⟩,⟨1898,by decide⟩,⟨1563,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨1899,by decide⟩,⟨1563,by decide⟩] | 2 => ![⟨1900,by decide⟩,⟨1900,by decide⟩,⟨1789,by decide⟩] | 3 => ![⟨1901,by decide⟩,⟨1864,by decide⟩,⟨1790,by decide⟩] | 4 => ![⟨1902,by decide⟩,⟨1789,by decide⟩,⟨1789,by decide⟩] | 5 => ![⟨1900,by decide⟩,⟨1900,by decide⟩,⟨1903,by decide⟩] | 6 => ![⟨1904,by decide⟩,⟨1900,by decide⟩,⟨1793,by decide⟩] | _ => ![⟨1904,by decide⟩,⟨1905,by decide⟩,⟨1906,by decide⟩]

def ntree11RLLRRLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1907,by decide⟩,⟨1896,by decide⟩,⟨1796,by decide⟩] | 1 => ![⟨1908,by decide⟩,⟨1909,by decide⟩,⟨1793,by decide⟩] | 2 => ![⟨1858,by decide⟩,⟨1910,by decide⟩,⟨268,by decide⟩] | 3 => ![⟨1859,by decide⟩,⟨1911,by decide⟩,⟨270,by decide⟩] | 4 => ![⟨1912,by decide⟩,⟨1913,by decide⟩,⟨614,by decide⟩] | 5 => ![⟨1864,by decide⟩,⟨1914,by decide⟩,⟨270,by decide⟩] | 6 => ![⟨1858,by decide⟩,⟨1858,by decide⟩,⟨1578,by decide⟩] | _ => ![⟨1859,by decide⟩,⟨1859,by decide⟩,⟨1579,by decide⟩]

def ntree11RLLRRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLLRRLRRL i else ntree11RLLRRLRRR (i - 8)

def ntree11RLLRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLLRRLRL i else ntree11RLLRRLRR (i - 15)

def ntree11RLLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RLLRRLL i else ntree11RLLRRLR (i - 31)

def ntree11RLLRRRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1879,by decide⟩,⟨1915,by decide⟩,⟨1581,by decide⟩] | 1 => ![⟨1868,by decide⟩,⟨1910,by decide⟩,⟨1583,by decide⟩] | 2 => ![⟨1870,by decide⟩,⟨1911,by decide⟩,⟨1584,by decide⟩] | 3 => ![⟨1872,by decide⟩,⟨1914,by decide⟩,⟨1584,by decide⟩] | 4 => ![⟨1916,by decide⟩,⟨1900,by decide⟩,⟨1804,by decide⟩] | 5 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨1579,by decide⟩] | _ => ![⟨1789,by decide⟩,⟨1789,by decide⟩,⟨1917,by decide⟩]

def ntree11RLLRRRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1793,by decide⟩,⟨1918,by decide⟩,⟨1919,by decide⟩] | 1 => ![⟨1920,by decide⟩,⟨1921,by decide⟩,⟨1808,by decide⟩] | 2 => ![⟨1922,by decide⟩,⟨1858,by decide⟩,⟨625,by decide⟩] | 3 => ![⟨1922,by decide⟩,⟨1910,by decide⟩,⟨759,by decide⟩] | 4 => ![⟨1923,by decide⟩,⟨1859,by decide⟩,⟨630,by decide⟩] | 5 => ![⟨1923,by decide⟩,⟨1911,by decide⟩,⟨760,by decide⟩] | 6 => ![⟨1924,by decide⟩,⟨1896,by decide⟩,⟨632,by decide⟩] | _ => ![⟨1925,by decide⟩,⟨1864,by decide⟩,⟨635,by decide⟩]

def ntree11RLLRRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLLRRRLLL i else ntree11RLLRRRLLR (i - 7)

def ntree11RLLRRRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1925,by decide⟩,⟨1914,by decide⟩,⟨762,by decide⟩] | 1 => ![⟨1926,by decide⟩,⟨1789,by decide⟩,⟨1789,by decide⟩] | 2 => ![⟨1926,by decide⟩,⟨1918,by decide⟩,⟨1918,by decide⟩] | 3 => ![⟨1927,by decide⟩,⟨1909,by decide⟩,⟨1804,by decide⟩] | 4 => ![⟨1928,by decide⟩,⟨1928,by decide⟩,⟨1444,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨1929,by decide⟩,⟨1930,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1931,by decide⟩] | _ => ![⟨1932,by decide⟩,⟨1928,by decide⟩,⟨1821,by decide⟩]

def ntree11RLLRRRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1933,by decide⟩,⟨1864,by decide⟩,⟨1822,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨1934,by decide⟩,⟨1934,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨1934,by decide⟩,⟨1935,by decide⟩] | 3 => ![⟨1936,by decide⟩,⟨1864,by decide⟩,⟨1460,by decide⟩] | 4 => ![⟨1937,by decide⟩,⟨1874,by decide⟩,⟨1826,by decide⟩] | 5 => ![⟨1938,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨1939,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1940,by decide⟩]

def ntree11RLLRRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLLRRRLRL i else ntree11RLLRRRLRR (i - 8)

def ntree11RLLRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLLRRRLL i else ntree11RLLRRRLR (i - 15)

def ntree11RLLRRRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1941,by decide⟩,⟨1874,by decide⟩,⟨655,by decide⟩] | 1 => ![⟨1942,by decide⟩,⟨1864,by decide⟩,⟨135,by decide⟩] | 2 => ![⟨1558,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1943,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩] | 4 => ![⟨1944,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨581,by decide⟩,⟨1521,by decide⟩,⟨1945,by decide⟩] | _ => ![⟨1559,by decide⟩,⟨1946,by decide⟩,⟨10,by decide⟩]

def ntree11RLLRRRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1559,by decide⟩,⟨1559,by decide⟩,⟨775,by decide⟩] | 1 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨1625,by decide⟩] | 2 => ![⟨1936,by decide⟩,⟨1914,by decide⟩,⟨1630,by decide⟩] | 3 => ![⟨1938,by decide⟩,⟨270,by decide⟩,⟨270,by decide⟩] | 4 => ![⟨1947,by decide⟩,⟨10,by decide⟩,⟨581,by decide⟩] | 5 => ![⟨1948,by decide⟩,⟨270,by decide⟩,⟨270,by decide⟩] | 6 => ![⟨1895,by decide⟩,⟨1883,by decide⟩,⟨805,by decide⟩] | _ => ![⟨1576,by decide⟩,⟨1949,by decide⟩,⟨47,by decide⟩]

def ntree11RLLRRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLLRRRRLL i else ntree11RLLRRRRLR (i - 7)

def ntree11RLLRRRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1950,by decide⟩,⟨1928,by decide⟩,⟨1852,by decide⟩] | 1 => ![⟨1951,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩] | 2 => ![⟨1592,by decide⟩,⟨816,by decide⟩,⟨816,by decide⟩] | 3 => ![⟨1951,by decide⟩,⟨817,by decide⟩,⟨817,by decide⟩] | 4 => ![⟨1592,by decide⟩,⟨1764,by decide⟩,⟨818,by decide⟩] | 5 => ![⟨1594,by decide⟩,⟨1952,by decide⟩,⟨820,by decide⟩] | 6 => ![⟨1953,by decide⟩,⟨1953,by decide⟩,⟨1954,by decide⟩] | _ => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨684,by decide⟩]

def ntree11RLLRRRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1953,by decide⟩,⟨1953,by decide⟩,⟨1955,by decide⟩] | 1 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨1331,by decide⟩] | 2 => ![⟨1748,by decide⟩,⟨1494,by decide⟩,⟨1863,by decide⟩] | 3 => ![⟨1956,by decide⟩,⟨1953,by decide⟩,⟨1957,by decide⟩] | 4 => ![⟨1864,by decide⟩,⟨1958,by decide⟩,⟨1758,by decide⟩] | 5 => ![⟨1864,by decide⟩,⟨1958,by decide⟩,⟨1760,by decide⟩] | 6 => ![⟨1872,by decide⟩,⟨1959,by decide⟩,⟨1333,by decide⟩] | _ => ![⟨1322,by decide⟩,⟨1960,by decide⟩,⟨1322,by decide⟩]

def ntree11RLLRRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLLRRRRRL i else ntree11RLLRRRRRR (i - 8)

def ntree11RLLRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLLRRRRL i else ntree11RLLRRRRR (i - 15)

def ntree11RLLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RLLRRRL i else ntree11RLLRRRR (i - 31)

def ntree11RLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11RLLRRL i else ntree11RLLRRR (i - 62)

def ntree11RLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 124 then ntree11RLLRL i else ntree11RLLRR (i - 124)

def ntree11RLL (i : Nat) : Fin 3 → Fin 3109 := if i < 247 then ntree11RLLL i else ntree11RLLR (i - 247)

def ntree11RLRLLLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1961,by decide⟩,⟨1953,by decide⟩,⟨1962,by decide⟩] | 1 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨1655,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨1494,by decide⟩,⟨1494,by decide⟩] | 3 => ![⟨1963,by decide⟩,⟨1964,by decide⟩,⟨1965,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨1766,by decide⟩,⟨1766,by decide⟩] | 5 => ![⟨1872,by decide⟩,⟨1966,by decide⟩,⟨1361,by decide⟩] | _ => ![⟨1322,by decide⟩,⟨1967,by decide⟩,⟨1322,by decide⟩]

def ntree11RLRLLLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨1662,by decide⟩,⟨684,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨1663,by decide⟩,⟨1887,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨1662,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1864,by decide⟩,⟨1966,by decide⟩,⟨65,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨1967,by decide⟩,⟨1331,by decide⟩] | 5 => ![⟨514,by decide⟩,⟨1968,by decide⟩,⟨514,by decide⟩] | 6 => ![⟨1969,by decide⟩,⟨1864,by decide⟩,⟨877,by decide⟩] | _ => ![⟨1970,by decide⟩,⟨1970,by decide⟩,⟨878,by decide⟩]

def ntree11RLRLLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLRLLLLLL i else ntree11RLRLLLLLR (i - 7)

def ntree11RLRLLLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1971,by decide⟩,⟨1389,by decide⟩,⟨877,by decide⟩] | 1 => ![⟨1864,by decide⟩,⟨1972,by decide⟩,⟨1973,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨1974,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨1975,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1389,by decide⟩,⟨1389,by decide⟩,⟨684,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨1976,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1977,by decide⟩,⟨1864,by decide⟩,⟨578,by decide⟩]

def ntree11RLRLLLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1776,by decide⟩,⟨1389,by decide⟩,⟨578,by decide⟩] | 1 => ![⟨1977,by decide⟩,⟨1864,by decide⟩,⟨731,by decide⟩] | 2 => ![⟨578,by decide⟩,⟨10,by decide⟩,⟨578,by decide⟩] | 3 => ![⟨1781,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨1978,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨1979,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1864,by decide⟩,⟨1980,by decide⟩,⟨1787,by decide⟩]

def ntree11RLRLLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLRLLLLRL i else ntree11RLRLLLLRR (i - 7)

def ntree11RLRLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLRLLLLL i else ntree11RLRLLLLR (i - 15)

def ntree11RLRLLLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨1981,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨1981,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1872,by decide⟩,⟨1980,by decide⟩,⟨1788,by decide⟩] | 3 => ![⟨1322,by decide⟩,⟨1981,by decide⟩,⟨1322,by decide⟩] | 4 => ![⟨1322,by decide⟩,⟨1982,by decide⟩,⟨1322,by decide⟩] | 5 => ![⟨1969,by decide⟩,⟨1958,by decide⟩,⟨1983,by decide⟩] | _ => ![⟨1386,by decide⟩,⟨384,by decide⟩,⟨10,by decide⟩]

def ntree11RLRLLLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1389,by decide⟩,⟨1984,by decide⟩,⟨1563,by decide⟩] | 1 => ![⟨1985,by decide⟩,⟨1970,by decide⟩,⟨1986,by decide⟩] | 2 => ![⟨1987,by decide⟩,⟨1987,by decide⟩,⟨895,by decide⟩] | 3 => ![⟨1988,by decide⟩,⟨1987,by decide⟩,⟨897,by decide⟩] | 4 => ![⟨1989,by decide⟩,⟨1987,by decide⟩,⟨900,by decide⟩] | 5 => ![⟨877,by decide⟩,⟨1766,by decide⟩,⟨1990,by decide⟩] | 6 => ![⟨1991,by decide⟩,⟨1987,by decide⟩,⟨1992,by decide⟩] | _ => ![⟨1992,by decide⟩,⟨895,by decide⟩,⟨1992,by decide⟩]

def ntree11RLRLLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLRLLLRLL i else ntree11RLRLLLRLR (i - 7)

def ntree11RLRLLLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1993,by decide⟩,⟨1970,by decide⟩,⟨913,by decide⟩] | 1 => ![⟨1994,by decide⟩,⟨1864,by decide⟩,⟨924,by decide⟩] | 2 => ![⟨1995,by decide⟩,⟨1864,by decide⟩,⟨630,by decide⟩] | 3 => ![⟨1996,by decide⟩,⟨1970,by decide⟩,⟨917,by decide⟩] | 4 => ![⟨1995,by decide⟩,⟨1914,by decide⟩,⟨760,by decide⟩] | 5 => ![⟨630,by decide⟩,⟨1662,by decide⟩,⟨630,by decide⟩] | 6 => ![⟨1811,by decide⟩,⟨1714,by decide⟩,⟨760,by decide⟩] | _ => ![⟨10,by decide⟩,⟨1997,by decide⟩,⟨10,by decide⟩]

def ntree11RLRLLLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨1817,by decide⟩] | 1 => ![⟨47,by decide⟩,⟨1997,by decide⟩,⟨47,by decide⟩] | 2 => ![⟨1998,by decide⟩,⟨1864,by decide⟩,⟨1999,by decide⟩] | 3 => ![⟨2000,by decide⟩,⟨1389,by decide⟩,⟨1999,by decide⟩] | 4 => ![⟨2001,by decide⟩,⟨2001,by decide⟩,⟨2002,by decide⟩] | 5 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨1940,by decide⟩] | 6 => ![⟨2003,by decide⟩,⟨1864,by decide⟩,⟨469,by decide⟩] | _ => ![⟨2004,by decide⟩,⟨1874,by decide⟩,⟨929,by decide⟩]

def ntree11RLRLLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLRLLLRRL i else ntree11RLRLLLRRR (i - 8)

def ntree11RLRLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLRLLLRL i else ntree11RLRLLLRR (i - 15)

def ntree11RLRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 30 then ntree11RLRLLLL i else ntree11RLRLLLR (i - 30)

def ntree11RLRLLRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2005,by decide⟩,⟨1970,by decide⟩,⟨932,by decide⟩] | 1 => ![⟨2006,by decide⟩,⟨1831,by decide⟩,⟨469,by decide⟩] | 2 => ![⟨2007,by decide⟩,⟨1832,by decide⟩,⟨929,by decide⟩] | 3 => ![⟨2008,by decide⟩,⟨1831,by decide⟩,⟨877,by decide⟩] | 4 => ![⟨1864,by decide⟩,⟨1959,by decide⟩,⟨40,by decide⟩] | 5 => ![⟨1389,by decide⟩,⟨2009,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1864,by decide⟩,⟨2010,by decide⟩,⟨2011,by decide⟩]

def ntree11RLRLLRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1953,by decide⟩,⟨2012,by decide⟩,⟨2013,by decide⟩] | 1 => ![⟨2014,by decide⟩,⟨2014,by decide⟩,⟨895,by decide⟩] | 2 => ![⟨2015,by decide⟩,⟨2014,by decide⟩,⟨897,by decide⟩] | 3 => ![⟨1831,by decide⟩,⟨2016,by decide⟩,⟨270,by decide⟩] | 4 => ![⟨1411,by decide⟩,⟨2017,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨2018,by decide⟩] | 6 => ![⟨1831,by decide⟩,⟨2019,by decide⟩,⟨816,by decide⟩] | _ => ![⟨1832,by decide⟩,⟨2020,by decide⟩,⟨817,by decide⟩]

def ntree11RLRLLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLRLLRLLL i else ntree11RLRLLRLLR (i - 7)

def ntree11RLRLLRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨954,by decide⟩,⟨10,by decide⟩,⟨2021,by decide⟩] | 1 => ![⟨1748,by decide⟩,⟨11,by decide⟩,⟨2022,by decide⟩] | 2 => ![⟨2023,by decide⟩,⟨952,by decide⟩,⟨2022,by decide⟩] | 3 => ![⟨2024,by decide⟩,⟨2024,by decide⟩,⟨2024,by decide⟩] | 4 => ![⟨2025,by decide⟩,⟨2025,by decide⟩,⟨2024,by decide⟩] | 5 => ![⟨2026,by decide⟩,⟨2024,by decide⟩,⟨2026,by decide⟩] | 6 => ![⟨2027,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨2028,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩]

def ntree11RLRLLRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2029,by decide⟩,⟨2024,by decide⟩,⟨2029,by decide⟩] | 1 => ![⟨2030,by decide⟩,⟨2025,by decide⟩,⟨2029,by decide⟩] | 2 => ![⟨2031,by decide⟩,⟨951,by decide⟩,⟨1322,by decide⟩] | 3 => ![⟨2032,by decide⟩,⟨958,by decide⟩,⟨1756,by decide⟩] | 4 => ![⟨2024,by decide⟩,⟨2033,by decide⟩,⟨2033,by decide⟩] | 5 => ![⟨2027,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 6 => ![⟨2028,by decide⟩,⟨959,by decide⟩,⟨959,by decide⟩] | _ => ![⟨1756,by decide⟩,⟨959,by decide⟩,⟨2034,by decide⟩]

def ntree11RLRLLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLRLLRLRL i else ntree11RLRLLRLRR (i - 8)

def ntree11RLRLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLRLLRLL i else ntree11RLRLLRLR (i - 15)

def ntree11RLRLLRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2031,by decide⟩,⟨952,by decide⟩,⟨1334,by decide⟩] | 1 => ![⟨2032,by decide⟩,⟨962,by decide⟩,⟨2034,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2035,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨2035,by decide⟩] | 4 => ![⟨2036,by decide⟩,⟨952,by decide⟩,⟨1339,by decide⟩] | 5 => ![⟨1342,by decide⟩,⟨505,by decide⟩,⟨2037,by decide⟩] | _ => ![⟨1338,by decide⟩,⟨506,by decide⟩,⟨2037,by decide⟩]

def ntree11RLRLLRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2038,by decide⟩,⟨2038,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨2039,by decide⟩,⟨10,by decide⟩,⟨1338,by decide⟩] | 2 => ![⟨2040,by decide⟩,⟨2038,by decide⟩,⟨1322,by decide⟩] | 3 => ![⟨2041,by decide⟩,⟨983,by decide⟩,⟨1350,by decide⟩] | 4 => ![⟨1357,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1364,by decide⟩,⟨991,by decide⟩,⟨1322,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨2042,by decide⟩,⟨2043,by decide⟩] | _ => ![⟨10,by decide⟩,⟨2044,by decide⟩,⟨2045,by decide⟩]

def ntree11RLRLLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLRLLRRLL i else ntree11RLRLLRRLR (i - 7)

def ntree11RLRLLRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2046,by decide⟩] | 1 => ![⟨2036,by decide⟩,⟨996,by decide⟩,⟨2047,by decide⟩] | 2 => ![⟨1338,by decide⟩,⟨549,by decide⟩,⟨2047,by decide⟩] | 3 => ![⟨2048,by decide⟩,⟨2024,by decide⟩,⟨2048,by decide⟩] | 4 => ![⟨2049,by decide⟩,⟨10,by decide⟩,⟨2049,by decide⟩] | 5 => ![⟨2050,by decide⟩,⟨514,by decide⟩,⟨2050,by decide⟩] | 6 => ![⟨2051,by decide⟩,⟨14,by decide⟩,⟨2049,by decide⟩] | _ => ![⟨2052,by decide⟩,⟨515,by decide⟩,⟨2050,by decide⟩]

def ntree11RLRLLRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2053,by decide⟩,⟨2024,by decide⟩,⟨2024,by decide⟩] | 1 => ![⟨2054,by decide⟩,⟨951,by decide⟩,⟨2049,by decide⟩] | 2 => ![⟨2055,by decide⟩,⟨958,by decide⟩,⟨2050,by decide⟩] | 3 => ![⟨2056,by decide⟩,⟨26,by decide⟩,⟨2057,by decide⟩] | 4 => ![⟨2057,by decide⟩,⟨27,by decide⟩,⟨2057,by decide⟩] | 5 => ![⟨2024,by decide⟩,⟨2058,by decide⟩,⟨2058,by decide⟩] | 6 => ![⟨2059,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨2059,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11RLRLLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLRLLRRRL i else ntree11RLRLLRRRR (i - 8)

def ntree11RLRLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLRLLRRL i else ntree11RLRLLRRR (i - 15)

def ntree11RLRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RLRLLRL i else ntree11RLRLLRR (i - 31)

def ntree11RLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 61 then ntree11RLRLLL i else ntree11RLRLLR (i - 61)

def ntree11RLRLRLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2059,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨2060,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩] | 2 => ![⟨514,by decide⟩,⟨514,by decide⟩,⟨2061,by decide⟩] | 3 => ![⟨951,by decide⟩,⟨951,by decide⟩,⟨1378,by decide⟩] | 4 => ![⟨958,by decide⟩,⟨958,by decide⟩,⟨2061,by decide⟩] | 5 => ![⟨2059,by decide⟩,⟨569,by decide⟩,⟨1378,by decide⟩] | _ => ![⟨2062,by decide⟩,⟨1000,by decide⟩,⟨1378,by decide⟩]

def ntree11RLRLRLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1391,by decide⟩,⟨1391,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨581,by decide⟩,⟨1002,by decide⟩,⟨2063,by decide⟩] | 2 => ![⟨2064,by decide⟩,⟨1384,by decide⟩,⟨2064,by decide⟩] | 3 => ![⟨954,by decide⟩,⟨10,by decide⟩,⟨954,by decide⟩] | 4 => ![⟨2065,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1384,by decide⟩,⟨2066,by decide⟩,⟨2066,by decide⟩] | 6 => ![⟨2067,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩] | _ => ![⟨2068,by decide⟩,⟨11,by decide⟩,⟨1011,by decide⟩]

def ntree11RLRLRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLRLRLLLL i else ntree11RLRLRLLLR (i - 7)

def ntree11RLRLRLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨2069,by decide⟩,⟨2069,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2070,by decide⟩] | 2 => ![⟨2024,by decide⟩,⟨2071,by decide⟩,⟨2071,by decide⟩] | 3 => ![⟨1312,by decide⟩,⟨2069,by decide⟩,⟨2069,by decide⟩] | 4 => ![⟨2024,by decide⟩,⟨2024,by decide⟩,⟨2024,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨2072,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨1322,by decide⟩,⟨1002,by decide⟩,⟨2073,by decide⟩] | _ => ![⟨2029,by decide⟩,⟨2074,by decide⟩,⟨2029,by decide⟩]

def ntree11RLRLRLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1322,by decide⟩,⟨2069,by decide⟩,⟨2075,by decide⟩] | 1 => ![⟨1325,by decide⟩,⟨2076,by decide⟩,⟨2075,by decide⟩] | 2 => ![⟨1789,by decide⟩,⟨2077,by decide⟩,⟨2077,by decide⟩] | 3 => ![⟨2078,by decide⟩,⟨2079,by decide⟩,⟨2079,by decide⟩] | 4 => ![⟨2080,by decide⟩,⟨2077,by decide⟩,⟨2077,by decide⟩] | 5 => ![⟨2081,by decide⟩,⟨2033,by decide⟩,⟨2033,by decide⟩] | 6 => ![⟨2078,by decide⟩,⟨2078,by decide⟩,⟨2078,by decide⟩] | _ => ![⟨2082,by decide⟩,⟨2078,by decide⟩,⟨2082,by decide⟩]

def ntree11RLRLRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLRLRLLRL i else ntree11RLRLRLLRR (i - 8)

def ntree11RLRLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLRLRLLL i else ntree11RLRLRLLR (i - 15)

def ntree11RLRLRLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1793,by decide⟩,⟨2077,by decide⟩,⟨2083,by decide⟩] | 1 => ![⟨2084,by decide⟩,⟨2085,by decide⟩,⟨2083,by decide⟩] | 2 => ![⟨2086,by decide⟩,⟨1416,by decide⟩,⟨964,by decide⟩] | 3 => ![⟨963,by decide⟩,⟨1418,by decide⟩,⟨963,by decide⟩] | 4 => ![⟨581,by decide⟩,⟨2087,by decide⟩,⟨2088,by decide⟩] | 5 => ![⟨1415,by decide⟩,⟨1415,by decide⟩,⟨2035,by decide⟩] | _ => ![⟨10,by decide⟩,⟨2087,by decide⟩,⟨2087,by decide⟩]

def ntree11RLRLRLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨2089,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩] | 2 => ![⟨1801,by decide⟩,⟨1416,by decide⟩,⟨1011,by decide⟩] | 3 => ![⟨581,by decide⟩,⟨1418,by decide⟩,⟨581,by decide⟩] | 4 => ![⟨2090,by decide⟩,⟨2091,by decide⟩,⟨11,by decide⟩] | 5 => ![⟨2092,by decide⟩,⟨2093,by decide⟩,⟨581,by decide⟩] | 6 => ![⟨2094,by decide⟩,⟨2093,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1357,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩]

def ntree11RLRLRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLRLRLRLL i else ntree11RLRLRLRLR (i - 7)

def ntree11RLRLRLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨963,by decide⟩,⟨2069,by decide⟩,⟨2095,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨2096,by decide⟩,⟨2069,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2097,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1322,by decide⟩,⟨2087,by decide⟩,⟨2098,by decide⟩] | 5 => ![⟨1322,by decide⟩,⟨2096,by decide⟩,⟨2075,by decide⟩] | 6 => ![⟨2099,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | _ => ![⟨2100,by decide⟩,⟨1789,by decide⟩,⟨1789,by decide⟩]

def ntree11RLRLRLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2101,by decide⟩,⟨1766,by decide⟩,⟨1766,by decide⟩] | 1 => ![⟨2102,by decide⟩,⟨2091,by decide⟩,⟨1334,by decide⟩] | 2 => ![⟨2103,by decide⟩,⟨2104,by decide⟩,⟨1793,by decide⟩] | 3 => ![⟨2105,by decide⟩,⟨2093,by decide⟩,⟨1322,by decide⟩] | 4 => ![⟨2106,by decide⟩,⟨1391,by decide⟩,⟨963,by decide⟩] | 5 => ![⟨2106,by decide⟩,⟨1431,by decide⟩,⟨963,by decide⟩] | 6 => ![⟨1384,by decide⟩,⟨2107,by decide⟩,⟨2107,by decide⟩] | _ => ![⟨10,by decide⟩,⟨549,by decide⟩,⟨549,by decide⟩]

def ntree11RLRLRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLRLRLRRL i else ntree11RLRLRLRRR (i - 8)

def ntree11RLRLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLRLRLRL i else ntree11RLRLRLRR (i - 15)

def ntree11RLRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RLRLRLL i else ntree11RLRLRLR (i - 31)

def ntree11RLRLRRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨1418,by decide⟩,⟨1021,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1021,by decide⟩] | 2 => ![⟨963,by decide⟩,⟨2108,by decide⟩,⟨2109,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨2108,by decide⟩,⟨2108,by decide⟩] | 4 => ![⟨594,by decide⟩,⟨2110,by decide⟩,⟨2108,by decide⟩] | 5 => ![⟨2024,by decide⟩,⟨2111,by decide⟩,⟨2111,by decide⟩] | _ => ![⟨1357,by decide⟩,⟨2108,by decide⟩,⟨2108,by decide⟩]

def ntree11RLRLRRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2049,by decide⟩,⟨10,by decide⟩,⟨2049,by decide⟩] | 1 => ![⟨2049,by decide⟩,⟨10,by decide⟩,⟨2112,by decide⟩] | 2 => ![⟨2113,by decide⟩,⟨594,by decide⟩,⟨2049,by decide⟩] | 3 => ![⟨2024,by decide⟩,⟨2114,by decide⟩,⟨2024,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨2108,by decide⟩,⟨2108,by decide⟩] | 5 => ![⟨25,by decide⟩,⟨2115,by decide⟩,⟨2108,by decide⟩] | 6 => ![⟨2116,by decide⟩,⟨25,by decide⟩,⟨2049,by decide⟩] | _ => ![⟨1789,by decide⟩,⟨2117,by decide⟩,⟨2117,by decide⟩]

def ntree11RLRLRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLRLRRLLL i else ntree11RLRLRRLLR (i - 7)

def ntree11RLRLRRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2118,by decide⟩,⟨2108,by decide⟩,⟨2108,by decide⟩] | 1 => ![⟨2119,by decide⟩,⟨2024,by decide⟩,⟨2024,by decide⟩] | 2 => ![⟨2078,by decide⟩,⟨2120,by decide⟩,⟨2120,by decide⟩] | 3 => ![⟨2121,by decide⟩,⟨2117,by decide⟩,⟨2117,by decide⟩] | 4 => ![⟨2122,by decide⟩,⟨2058,by decide⟩,⟨2058,by decide⟩] | 5 => ![⟨2123,by decide⟩,⟨2024,by decide⟩,⟨2123,by decide⟩] | 6 => ![⟨1789,by decide⟩,⟨1789,by decide⟩,⟨2124,by decide⟩] | _ => ![⟨635,by decide⟩,⟨2108,by decide⟩,⟨2125,by decide⟩]

def ntree11RLRLRRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2126,by decide⟩,⟨2126,by decide⟩,⟨2124,by decide⟩] | 1 => ![⟨2127,by decide⟩,⟨2115,by decide⟩,⟨2125,by decide⟩] | 2 => ![⟨2128,by decide⟩,⟨1802,by decide⟩,⟨1378,by decide⟩] | 3 => ![⟨2129,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨644,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨2130,by decide⟩,⟨1448,by decide⟩,⟨2064,by decide⟩] | 6 => ![⟨2131,by decide⟩,⟨1449,by decide⟩,⟨2021,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11RLRLRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLRLRRLRL i else ntree11RLRLRRLRR (i - 8)

def ntree11RLRLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLRLRRLL i else ntree11RLRLRRLR (i - 15)

def ntree11RLRLRRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨514,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨2070,by decide⟩] | 2 => ![⟨2027,by decide⟩,⟨1397,by decide⟩,⟨1397,by decide⟩] | 3 => ![⟨1317,by decide⟩,⟨1201,by decide⟩,⟨1317,by decide⟩] | 4 => ![⟨1312,by decide⟩,⟨10,by decide⟩,⟨1021,by decide⟩] | 5 => ![⟨1828,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | _ => ![⟨1829,by decide⟩,⟨959,by decide⟩,⟨959,by decide⟩]

def ntree11RLRLRRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2132,by decide⟩,⟨1385,by decide⟩,⟨1385,by decide⟩] | 1 => ![⟨1384,by decide⟩,⟨1384,by decide⟩,⟨1384,by decide⟩] | 2 => ![⟨581,by decide⟩,⟨10,by decide⟩,⟨581,by decide⟩] | 3 => ![⟨2133,by decide⟩,⟨10,by decide⟩,⟨581,by decide⟩] | 4 => ![⟨2134,by decide⟩,⟨2135,by decide⟩,⟨2136,by decide⟩] | 5 => ![⟨2137,by decide⟩,⟨2138,by decide⟩,⟨2139,by decide⟩] | 6 => ![⟨2140,by decide⟩,⟨2141,by decide⟩,⟨2142,by decide⟩] | _ => ![⟨2143,by decide⟩,⟨2093,by decide⟩,⟨1338,by decide⟩]

def ntree11RLRLRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLRLRRRLL i else ntree11RLRLRRRLR (i - 7)

def ntree11RLRLRRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2027,by decide⟩,⟨10,by decide⟩,⟨2097,by decide⟩] | 1 => ![⟨1338,by decide⟩,⟨1838,by decide⟩,⟨2144,by decide⟩] | 2 => ![⟨2145,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨2145,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨2145,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨675,by decide⟩,⟨2146,by decide⟩,⟨2147,by decide⟩] | 6 => ![⟨2148,by decide⟩,⟨1384,by decide⟩,⟨1384,by decide⟩] | _ => ![⟨675,by decide⟩,⟨2149,by decide⟩,⟨2045,by decide⟩]

def ntree11RLRLRRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2150,by decide⟩,⟨1838,by decide⟩,⟨2151,by decide⟩] | 1 => ![⟨2150,by decide⟩,⟨10,by decide⟩,⟨1338,by decide⟩] | 2 => ![⟨2049,by decide⟩,⟨10,by decide⟩,⟨2049,by decide⟩] | 3 => ![⟨2050,by decide⟩,⟨514,by decide⟩,⟨2050,by decide⟩] | 4 => ![⟨2051,by decide⟩,⟨14,by decide⟩,⟨2112,by decide⟩] | 5 => ![⟨1437,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨2145,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨2152,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩]

def ntree11RLRLRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLRLRRRRL i else ntree11RLRLRRRRR (i - 8)

def ntree11RLRLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLRLRRRL i else ntree11RLRLRRRR (i - 15)

def ntree11RLRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RLRLRRL i else ntree11RLRLRRR (i - 31)

def ntree11RLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11RLRLRL i else ntree11RLRLRR (i - 62)

def ntree11RLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 123 then ntree11RLRLL i else ntree11RLRLR (i - 123)

def ntree11RLRRLLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2059,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨2153,by decide⟩,⟨1384,by decide⟩,⟨1384,by decide⟩] | 2 => ![⟨635,by decide⟩,⟨2154,by decide⟩,⟨635,by decide⟩] | 3 => ![⟨1864,by decide⟩,⟨2155,by decide⟩,⟨2156,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨2157,by decide⟩,⟨2158,by decide⟩] | 5 => ![⟨2159,by decide⟩,⟨2155,by decide⟩,⟨2160,by decide⟩] | _ => ![⟨2159,by decide⟩,⟨1864,by decide⟩,⟨1317,by decide⟩]

def ntree11RLRRLLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1093,by decide⟩,⟨2157,by decide⟩,⟨2161,by decide⟩] | 1 => ![⟨2162,by decide⟩,⟨1864,by decide⟩,⟨954,by decide⟩] | 2 => ![⟨1493,by decide⟩,⟨502,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨2163,by decide⟩,⟨1120,by decide⟩,⟨1748,by decide⟩] | 4 => ![⟨1748,by decide⟩,⟨2157,by decide⟩,⟨2164,by decide⟩] | 5 => ![⟨2165,by decide⟩,⟨2165,by decide⟩,⟨2024,by decide⟩] | 6 => ![⟨2166,by decide⟩,⟨2165,by decide⟩,⟨2026,by decide⟩] | _ => ![⟨2167,by decide⟩,⟨2024,by decide⟩,⟨2024,by decide⟩]

def ntree11RLRRLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLRRLLLLL i else ntree11RLRRLLLLR (i - 7)

def ntree11RLRRLLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2168,by decide⟩,⟨2165,by decide⟩,⟨2029,by decide⟩] | 1 => ![⟨2169,by decide⟩,⟨1101,by decide⟩,⟨1756,by decide⟩] | 2 => ![⟨2170,by decide⟩,⟨2171,by decide⟩,⟨1327,by decide⟩] | 3 => ![⟨2172,by decide⟩,⟨2173,by decide⟩,⟨1322,by decide⟩] | 4 => ![⟨163,by decide⟩,⟨163,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1510,by decide⟩,⟨2174,by decide⟩,⟨1322,by decide⟩] | 6 => ![⟨2175,by decide⟩,⟨1864,by decide⟩,⟨963,by decide⟩] | _ => ![⟨2175,by decide⟩,⟨2155,by decide⟩,⟨2176,by decide⟩]

def ntree11RLRRLLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨963,by decide⟩,⟨2157,by decide⟩,⟨2177,by decide⟩] | 1 => ![⟨2178,by decide⟩,⟨1864,by decide⟩,⟨1338,by decide⟩] | 2 => ![⟨1338,by decide⟩,⟨2157,by decide⟩,⟨2179,by decide⟩] | 3 => ![⟨2180,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨2181,by decide⟩,⟨1120,by decide⟩,⟨1338,by decide⟩] | 5 => ![⟨2180,by decide⟩,⟨153,by decide⟩,⟨2182,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2183,by decide⟩] | _ => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨2184,by decide⟩]

def ntree11RLRRLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLRRLLLRL i else ntree11RLRRLLLRR (i - 8)

def ntree11RLRRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLRRLLLL i else ntree11RLRRLLLR (i - 15)

def ntree11RLRRLLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2185,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1527,by decide⟩,⟨502,by decide⟩,⟨2186,by decide⟩] | 3 => ![⟨1338,by decide⟩,⟨502,by decide⟩,⟨1338,by decide⟩] | 4 => ![⟨2187,by decide⟩,⟨201,by decide⟩,⟨1338,by decide⟩] | 5 => ![⟨2188,by decide⟩,⟨1120,by decide⟩,⟨1322,by decide⟩] | _ => ![⟨2189,by decide⟩,⟨2190,by decide⟩,⟨1350,by decide⟩]

def ntree11RLRRLLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨201,by decide⟩,⟨201,by decide⟩,⟨2191,by decide⟩] | 1 => ![⟨1872,by decide⟩,⟨2192,by decide⟩,⟨2193,by decide⟩] | 2 => ![⟨1322,by decide⟩,⟨2194,by decide⟩,⟨2195,by decide⟩] | 3 => ![⟨1322,by decide⟩,⟨2196,by decide⟩,⟨1322,by decide⟩] | 4 => ![⟨1537,by decide⟩,⟨2197,by decide⟩,⟨2198,by decide⟩] | 5 => ![⟨2178,by decide⟩,⟨1864,by decide⟩,⟨2199,by decide⟩] | 6 => ![⟨2200,by decide⟩,⟨1874,by decide⟩,⟨997,by decide⟩] | _ => ![⟨2201,by decide⟩,⟨2165,by decide⟩,⟨2048,by decide⟩]

def ntree11RLRRLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLRRLLRLL i else ntree11RLRRLLRLR (i - 7)

def ntree11RLRRLLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2202,by decide⟩,⟨163,by decide⟩,⟨2049,by decide⟩] | 1 => ![⟨2203,by decide⟩,⟨1101,by decide⟩,⟨2050,by decide⟩] | 2 => ![⟨2204,by decide⟩,⟨2024,by decide⟩,⟨2024,by decide⟩] | 3 => ![⟨2205,by decide⟩,⟨163,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨2206,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩] | 5 => ![⟨2171,by decide⟩,⟨2171,by decide⟩,⟨27,by decide⟩] | 6 => ![⟨2207,by decide⟩,⟨2173,by decide⟩,⟨1338,by decide⟩] | _ => ![⟨1864,by decide⟩,⟨2208,by decide⟩,⟨2209,by decide⟩]

def ntree11RLRRLLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨2210,by decide⟩,⟨2210,by decide⟩] | 1 => ![⟨163,by decide⟩,⟨2211,by decide⟩,⟨2212,by decide⟩] | 2 => ![⟨1527,by decide⟩,⟨2213,by decide⟩,⟨2213,by decide⟩] | 3 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨1161,by decide⟩] | 4 => ![⟨1864,by decide⟩,⟨2214,by decide⟩,⟨1162,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨1162,by decide⟩,⟨1162,by decide⟩] | 6 => ![⟨2215,by decide⟩,⟨2215,by decide⟩,⟨1384,by decide⟩] | _ => ![⟨10,by decide⟩,⟨1162,by decide⟩,⟨1162,by decide⟩]

def ntree11RLRRLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLRRLLRRL i else ntree11RLRRLLRRR (i - 8)

def ntree11RLRRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLRRLLRL i else ntree11RLRRLLRR (i - 15)

def ntree11RLRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RLRRLLL i else ntree11RLRRLLR (i - 31)

def ntree11RLRRLRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2216,by decide⟩,⟨2215,by decide⟩,⟨2064,by decide⟩] | 1 => ![⟨2162,by decide⟩,⟨1864,by decide⟩,⟨1174,by decide⟩] | 2 => ![⟨581,by decide⟩,⟨1162,by decide⟩,⟨1170,by decide⟩] | 3 => ![⟨2165,by decide⟩,⟨2165,by decide⟩,⟨2217,by decide⟩] | 4 => ![⟨163,by decide⟩,⟨1171,by decide⟩,⟨1162,by decide⟩] | 5 => ![⟨1872,by decide⟩,⟨2218,by decide⟩,⟨2219,by decide⟩] | _ => ![⟨2168,by decide⟩,⟨2220,by decide⟩,⟨2221,by decide⟩]

def ntree11RLRRLRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1872,by decide⟩,⟨2214,by decide⟩,⟨2222,by decide⟩] | 1 => ![⟨1322,by decide⟩,⟨1162,by decide⟩,⟨2222,by decide⟩] | 2 => ![⟨2223,by decide⟩,⟨2223,by decide⟩,⟨2078,by decide⟩] | 3 => ![⟨2224,by decide⟩,⟨2223,by decide⟩,⟨2082,by decide⟩] | 4 => ![⟨1864,by decide⟩,⟨2225,by decide⟩,⟨1178,by decide⟩] | 5 => ![⟨2175,by decide⟩,⟨2225,by decide⟩,⟨1179,by decide⟩] | 6 => ![⟨2180,by decide⟩,⟨1178,by decide⟩,⟨1178,by decide⟩] | _ => ![⟨2226,by decide⟩,⟨10,by decide⟩,⟨581,by decide⟩]

def ntree11RLRRLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLRRLRLLL i else ntree11RLRRLRLLR (i - 7)

def ntree11RLRRLRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1895,by decide⟩,⟨2225,by decide⟩,⟨1185,by decide⟩] | 1 => ![⟨1558,by decide⟩,⟨1178,by decide⟩,⟨1178,by decide⟩] | 2 => ![⟨2180,by decide⟩,⟨751,by decide⟩,⟨1579,by decide⟩] | 3 => ![⟨1872,by decide⟩,⟨2225,by decide⟩,⟨2227,by decide⟩] | 4 => ![⟨1322,by decide⟩,⟨1178,by decide⟩,⟨2227,by decide⟩] | 5 => ![⟨2228,by decide⟩,⟨2228,by decide⟩,⟨1789,by decide⟩] | 6 => ![⟨2229,by decide⟩,⟨2228,by decide⟩,⟨1793,by decide⟩] | _ => ![⟨2230,by decide⟩,⟨1384,by decide⟩,⟨1384,by decide⟩]

def ntree11RLRRLRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2231,by decide⟩,⟨1178,by decide⟩,⟨1178,by decide⟩] | 1 => ![⟨2231,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨2049,by decide⟩,⟨1178,by decide⟩,⟨2232,by decide⟩] | 3 => ![⟨2202,by decide⟩,⟨1194,by decide⟩,⟨2232,by decide⟩] | 4 => ![⟨1864,by decide⟩,⟨2233,by decide⟩,⟨2234,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨2234,by decide⟩,⟨2234,by decide⟩] | 6 => ![⟨2165,by decide⟩,⟨2235,by decide⟩,⟨2236,by decide⟩] | _ => ![⟨2204,by decide⟩,⟨2236,by decide⟩,⟨2236,by decide⟩]

def ntree11RLRRLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLRRLRLRL i else ntree11RLRRLRLRR (i - 8)

def ntree11RLRRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLRRLRLL i else ntree11RLRRLRLR (i - 15)

def ntree11RLRRLRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨2237,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨1418,by decide⟩,⟨2237,by decide⟩] | 2 => ![⟨2049,by decide⟩,⟨270,by decide⟩,⟨2238,by decide⟩] | 3 => ![⟨2239,by decide⟩,⟨2165,by decide⟩,⟨2123,by decide⟩] | 4 => ![⟨2240,by decide⟩,⟨2078,by decide⟩,⟨2078,by decide⟩] | 5 => ![⟨1384,by decide⟩,⟨2241,by decide⟩,⟨2242,by decide⟩] | _ => ![⟨1093,by decide⟩,⟨2243,by decide⟩,⟨2244,by decide⟩]

def ntree11RLRRLRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨581,by decide⟩,⟨2157,by decide⟩,⟨2245,by decide⟩] | 1 => ![⟨1199,by decide⟩,⟨2157,by decide⟩,⟨2246,by decide⟩] | 2 => ![⟨1093,by decide⟩,⟨10,by decide⟩,⟨1608,by decide⟩] | 3 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨315,by decide⟩] | 4 => ![⟨1874,by decide⟩,⟨1874,by decide⟩,⟨1200,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨2243,by decide⟩,⟨2247,by decide⟩] | 6 => ![⟨1493,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨2248,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩]

def ntree11RLRRLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLRRLRRLL i else ntree11RLRRLRRLR (i - 7)

def ntree11RLRRLRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨514,by decide⟩,⟨514,by decide⟩,⟨2249,by decide⟩] | 1 => ![⟨1317,by decide⟩,⟨10,by decide⟩,⟨2250,by decide⟩] | 2 => ![⟨1895,by decide⟩,⟨1864,by decide⟩,⟨2251,by decide⟩] | 3 => ![⟨1557,by decide⟩,⟨1384,by decide⟩,⟨1384,by decide⟩] | 4 => ![⟨2178,by decide⟩,⟨1864,by decide⟩,⟨2252,by decide⟩] | 5 => ![⟨2253,by decide⟩,⟨2254,by decide⟩,⟨2255,by decide⟩] | 6 => ![⟨2256,by decide⟩,⟨2257,by decide⟩,⟨2258,by decide⟩] | _ => ![⟨2259,by decide⟩,⟨2260,by decide⟩,⟨2261,by decide⟩]

def ntree11RLRRLRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2262,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨2263,by decide⟩] | 2 => ![⟨1338,by decide⟩,⟨10,by decide⟩,⟨2264,by decide⟩] | 3 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨2265,by decide⟩] | 4 => ![⟨581,by decide⟩,⟨2266,by decide⟩,⟨2267,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨1527,by decide⟩,⟨2268,by decide⟩,⟨2268,by decide⟩] | _ => ![⟨2269,by decide⟩,⟨270,by decide⟩,⟨270,by decide⟩]

def ntree11RLRRLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLRRLRRRL i else ntree11RLRRLRRRR (i - 8)

def ntree11RLRRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLRRLRRL i else ntree11RLRRLRRR (i - 15)

def ntree11RLRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RLRRLRL i else ntree11RLRRLRR (i - 31)

def ntree11RLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11RLRRLL i else ntree11RLRRLR (i - 62)

def ntree11RLRRRLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1527,by decide⟩,⟨816,by decide⟩,⟨816,by decide⟩] | 1 => ![⟨2206,by decide⟩,⟨817,by decide⟩,⟨817,by decide⟩] | 2 => ![⟨2049,by decide⟩,⟨816,by decide⟩,⟨2270,by decide⟩] | 3 => ![⟨2050,by decide⟩,⟨817,by decide⟩,⟨2271,by decide⟩] | 4 => ![⟨1925,by decide⟩,⟨2272,by decide⟩,⟨2273,by decide⟩] | 5 => ![⟨1592,by decide⟩,⟨2274,by decide⟩,⟨2274,by decide⟩] | _ => ![⟨1592,by decide⟩,⟨2275,by decide⟩,⟨2275,by decide⟩]

def ntree11RLRRRLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1593,by decide⟩,⟨2276,by decide⟩,⟨2276,by decide⟩] | 1 => ![⟨1864,by decide⟩,⟨2277,by decide⟩,⟨11,by decide⟩] | 2 => ![⟨1953,by decide⟩,⟨2278,by decide⟩,⟨2279,by decide⟩] | 3 => ![⟨14,by decide⟩,⟨2280,by decide⟩,⟨2281,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨2282,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨2283,by decide⟩,⟨1953,by decide⟩,⟨2284,by decide⟩] | 6 => ![⟨1865,by decide⟩,⟨2277,by decide⟩,⟨2022,by decide⟩] | _ => ![⟨1749,by decide⟩,⟨2280,by decide⟩,⟨2285,by decide⟩]

def ntree11RLRRRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLRRRLLLL i else ntree11RLRRRLLLR (i - 7)

def ntree11RLRRRLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1748,by decide⟩,⟨2282,by decide⟩,⟨1748,by decide⟩] | 1 => ![⟨2286,by decide⟩,⟨2286,by decide⟩,⟨2287,by decide⟩] | 2 => ![⟨2288,by decide⟩,⟨2286,by decide⟩,⟨2289,by decide⟩] | 3 => ![⟨1874,by decide⟩,⟨2290,by decide⟩,⟨959,by decide⟩] | 4 => ![⟨514,by decide⟩,⟨2291,by decide⟩,⟨514,by decide⟩] | 5 => ![⟨2165,by decide⟩,⟨2292,by decide⟩,⟨2033,by decide⟩] | 6 => ![⟨2024,by decide⟩,⟨2293,by decide⟩,⟨2024,by decide⟩] | _ => ![⟨1872,by decide⟩,⟨2277,by decide⟩,⟨1334,by decide⟩]

def ntree11RLRRRLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1873,by decide⟩,⟨2290,by decide⟩,⟨2034,by decide⟩] | 1 => ![⟨1322,by decide⟩,⟨2282,by decide⟩,⟨1322,by decide⟩] | 2 => ![⟨1756,by decide⟩,⟨2291,by decide⟩,⟨1756,by decide⟩] | 3 => ![⟨2294,by decide⟩,⟨1864,by decide⟩,⟨1654,by decide⟩] | 4 => ![⟨2295,by decide⟩,⟨2295,by decide⟩,⟨391,by decide⟩] | 5 => ![⟨2296,by decide⟩,⟨2295,by decide⟩,⟨1658,by decide⟩] | 6 => ![⟨201,by decide⟩,⟨2297,by decide⟩,⟨1766,by decide⟩] | _ => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨2046,by decide⟩]

def ntree11RLRRRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLRRRLLRL i else ntree11RLRRRLLRR (i - 8)

def ntree11RLRRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLRRRLLL i else ntree11RLRRRLLR (i - 15)

def ntree11RLRRRLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2298,by decide⟩,⟨2165,by decide⟩,⟨2299,by decide⟩] | 1 => ![⟨2300,by decide⟩,⟨2025,by decide⟩,⟨2299,by decide⟩] | 2 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨1378,by decide⟩] | 3 => ![⟨1874,by decide⟩,⟨1874,by decide⟩,⟨2061,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨514,by decide⟩,⟨514,by decide⟩,⟨514,by decide⟩] | _ => ![⟨1969,by decide⟩,⟨2277,by decide⟩,⟨1252,by decide⟩]

def ntree11RLRRRLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨877,by decide⟩,⟨2282,by decide⟩,⟨877,by decide⟩] | 1 => ![⟨1864,by decide⟩,⟨2301,by decide⟩,⟨1002,by decide⟩] | 2 => ![⟨1493,by decide⟩,⟨1002,by decide⟩,⟨1002,by decide⟩] | 3 => ![⟨1781,by decide⟩,⟨2282,by decide⟩,⟨1223,by decide⟩] | 4 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨2070,by decide⟩] | 5 => ![⟨163,by decide⟩,⟨163,by decide⟩,⟨2070,by decide⟩] | 6 => ![⟨1872,by decide⟩,⟨2301,by decide⟩,⟨2073,by decide⟩] | _ => ![⟨1510,by decide⟩,⟨1262,by decide⟩,⟨2073,by decide⟩]

def ntree11RLRRRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLRRRLRLL i else ntree11RLRRRLRLR (i - 7)

def ntree11RLRRRLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2302,by decide⟩,⟨2292,by decide⟩,⟨2303,by decide⟩] | 1 => ![⟨2304,by decide⟩,⟨2293,by decide⟩,⟨2304,by decide⟩] | 2 => ![⟨1864,by decide⟩,⟨2305,by decide⟩,⟨2087,by decide⟩] | 3 => ![⟨2306,by decide⟩,⟨2307,by decide⟩,⟨449,by decide⟩] | 4 => ![⟨2308,by decide⟩,⟨2309,by decide⟩,⟨270,by decide⟩] | 5 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨2097,by decide⟩] | 6 => ![⟨1872,by decide⟩,⟨2305,by decide⟩,⟨2098,by decide⟩] | _ => ![⟨2310,by decide⟩,⟨2277,by decide⟩,⟨1699,by decide⟩]

def ntree11RLRRRLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2311,by decide⟩,⟨2282,by decide⟩,⟨1579,by decide⟩] | 1 => ![⟨2312,by decide⟩,⟨2297,by decide⟩,⟨1990,by decide⟩] | 2 => ![⟨2313,by decide⟩,⟨2307,by decide⟩,⟨1707,by decide⟩] | 3 => ![⟨2314,by decide⟩,⟨2309,by decide⟩,⟨1584,by decide⟩] | 4 => ![⟨2315,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11RLRRRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLRRRLRRL i else ntree11RLRRRLRRR (i - 8)

def ntree11RLRRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLRRRLRL i else ntree11RLRRRLRR (i - 15)

def ntree11RLRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RLRRRLL i else ntree11RLRRRLR (i - 31)

def ntree11RLRRRRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨1694,by decide⟩,⟨2070,by decide⟩] | 1 => ![⟨163,by decide⟩,⟨2316,by decide⟩,⟨2087,by decide⟩] | 2 => ![⟨1527,by decide⟩,⟨922,by decide⟩,⟨2070,by decide⟩] | 3 => ![⟨2317,by decide⟩,⟨1864,by decide⟩,⟨1718,by decide⟩] | 4 => ![⟨2318,by decide⟩,⟨2165,by decide⟩,⟨2319,by decide⟩] | 5 => ![⟨2320,by decide⟩,⟨1914,by decide⟩,⟨1729,by decide⟩] | _ => ![⟨2321,by decide⟩,⟨270,by decide⟩,⟨270,by decide⟩]

def ntree11RLRRRRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1953,by decide⟩,⟨1953,by decide⟩,⟨2322,by decide⟩] | 1 => ![⟨1646,by decide⟩,⟨14,by decide⟩,⟨2323,by decide⟩] | 2 => ![⟨2003,by decide⟩,⟨2277,by decide⟩,⟨470,by decide⟩] | 3 => ![⟨2004,by decide⟩,⟨2290,by decide⟩,⟨1292,by decide⟩] | 4 => ![⟨469,by decide⟩,⟨2282,by decide⟩,⟨469,by decide⟩] | 5 => ![⟨929,by decide⟩,⟨2291,by decide⟩,⟨929,by decide⟩] | 6 => ![⟨2324,by decide⟩,⟨2325,by decide⟩,⟨2326,by decide⟩] | _ => ![⟨2327,by decide⟩,⟨2328,by decide⟩,⟨2329,by decide⟩]

def ntree11RLRRRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLRRRRLLL i else ntree11RLRRRRLLR (i - 7)

def ntree11RLRRRRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2330,by decide⟩,⟨2331,by decide⟩,⟨2332,by decide⟩] | 1 => ![⟨1654,by decide⟩,⟨10,by decide⟩,⟨2333,by decide⟩] | 2 => ![⟨2145,by decide⟩,⟨2282,by decide⟩,⟨343,by decide⟩] | 3 => ![⟨2334,by decide⟩,⟨2282,by decide⟩,⟨1294,by decide⟩] | 4 => ![⟨1654,by decide⟩,⟨938,by decide⟩,⟨1654,by decide⟩] | 5 => ![⟨1656,by decide⟩,⟨940,by decide⟩,⟨2335,by decide⟩] | 6 => ![⟨1994,by decide⟩,⟨1864,by decide⟩,⟨1306,by decide⟩] | _ => ![⟨2336,by decide⟩,⟨1,by decide⟩,⟨2337,by decide⟩]

def ntree11RLRRRRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2338,by decide⟩,⟨2338,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨2339,by decide⟩] | 2 => ![⟨2340,by decide⟩,⟨5,by decide⟩,⟨2341,by decide⟩] | 3 => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨2342,by decide⟩] | 4 => ![⟨2343,by decide⟩,⟨9,by decide⟩,⟨2344,by decide⟩] | 5 => ![⟨2345,by decide⟩,⟨2345,by decide⟩,⟨1318,by decide⟩] | 6 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨2346,by decide⟩] | _ => ![⟨2347,by decide⟩,⟨11,by decide⟩,⟨2348,by decide⟩]

def ntree11RLRRRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLRRRRLRL i else ntree11RLRRRRLRR (i - 8)

def ntree11RLRRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLRRRRLL i else ntree11RLRRRRLR (i - 15)

def ntree11RLRRRRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2345,by decide⟩,⟨2345,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2349,by decide⟩] | 2 => ![⟨1310,by decide⟩,⟨16,by decide⟩,⟨2350,by decide⟩] | 3 => ![⟨1317,by decide⟩,⟨18,by decide⟩,⟨2351,by decide⟩] | 4 => ![⟨1320,by decide⟩,⟨20,by decide⟩,⟨2352,by decide⟩] | 5 => ![⟨1322,by decide⟩,⟨22,by decide⟩,⟨2353,by decide⟩] | _ => ![⟨1322,by decide⟩,⟨18,by decide⟩,⟨2354,by decide⟩]

def ntree11RLRRRRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1327,by decide⟩,⟨28,by decide⟩,⟨2355,by decide⟩] | 1 => ![⟨2356,by decide⟩,⟨11,by decide⟩,⟨2357,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2358,by decide⟩] | 3 => ![⟨2359,by decide⟩,⟨9,by decide⟩,⟨2360,by decide⟩] | 4 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨2361,by decide⟩] | 5 => ![⟨1322,by decide⟩,⟨35,by decide⟩,⟨2362,by decide⟩] | 6 => ![⟨2363,by decide⟩,⟨2345,by decide⟩,⟨1322,by decide⟩] | _ => ![⟨2364,by decide⟩,⟨8,by decide⟩,⟨2364,by decide⟩]

def ntree11RLRRRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RLRRRRRLL i else ntree11RLRRRRRLR (i - 7)

def ntree11RLRRRRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2364,by decide⟩,⟨41,by decide⟩,⟨2365,by decide⟩] | 1 => ![⟨2364,by decide⟩,⟨9,by decide⟩,⟨2366,by decide⟩] | 2 => ![⟨2367,by decide⟩,⟨2368,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨2369,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 4 => ![⟨2369,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨2370,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨1335,by decide⟩,⟨0,by decide⟩,⟨2371,by decide⟩] | _ => ![⟨2372,by decide⟩,⟨2373,by decide⟩,⟨1339,by decide⟩]

def ntree11RLRRRRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2374,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 1 => ![⟨2375,by decide⟩,⟨2373,by decide⟩,⟨11,by decide⟩] | 2 => ![⟨2374,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1338,by decide⟩,⟨2376,by decide⟩,⟨1338,by decide⟩] | 4 => ![⟨1338,by decide⟩,⟨10,by decide⟩,⟨2377,by decide⟩] | 5 => ![⟨2367,by decide⟩,⟨2367,by decide⟩,⟨0,by decide⟩] | 6 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨2375,by decide⟩,⟨2375,by decide⟩,⟨1344,by decide⟩]

def ntree11RLRRRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RLRRRRRRL i else ntree11RLRRRRRRR (i - 8)

def ntree11RLRRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RLRRRRRL i else ntree11RLRRRRRR (i - 15)

def ntree11RLRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RLRRRRL i else ntree11RLRRRRR (i - 31)

def ntree11RLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11RLRRRL i else ntree11RLRRRR (i - 62)

def ntree11RLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 124 then ntree11RLRRL i else ntree11RLRRR (i - 124)

def ntree11RLR (i : Nat) : Fin 3 → Fin 3109 := if i < 247 then ntree11RLRL i else ntree11RLRR (i - 247)

def ntree11RL (i : Nat) : Fin 3 → Fin 3109 := if i < 495 then ntree11RLL i else ntree11RLR (i - 495)

def ntree11RRLLLLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨2375,by decide⟩,⟨2375,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨2376,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1322,by decide⟩,⟨2376,by decide⟩,⟨1322,by decide⟩] | 4 => ![⟨2378,by decide⟩,⟨2379,by decide⟩,⟨1322,by decide⟩] | 5 => ![⟨1350,by decide⟩,⟨56,by decide⟩,⟨2380,by decide⟩] | _ => ![⟨1350,by decide⟩,⟨2381,by decide⟩,⟨1350,by decide⟩]

def ntree11RRLLLLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2382,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | 1 => ![⟨2382,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1354,by decide⟩,⟨10,by decide⟩,⟨2383,by decide⟩] | 3 => ![⟨2384,by decide⟩,⟨2375,by decide⟩,⟨1322,by decide⟩] | 4 => ![⟨1322,by decide⟩,⟨1477,by decide⟩,⟨1322,by decide⟩] | 5 => ![⟨2384,by decide⟩,⟨2373,by decide⟩,⟨1334,by decide⟩] | 6 => ![⟨2385,by decide⟩,⟨0,by decide⟩,⟨2385,by decide⟩] | _ => ![⟨2338,by decide⟩,⟨2386,by decide⟩,⟨0,by decide⟩]

def ntree11RRLLLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRLLLLLLL i else ntree11RRLLLLLLR (i - 7)

def ntree11RRLLLLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2385,by decide⟩,⟨0,by decide⟩,⟨2387,by decide⟩] | 1 => ![⟨2388,by decide⟩,⟨4,by decide⟩,⟨2388,by decide⟩] | 2 => ![⟨2388,by decide⟩,⟨4,by decide⟩,⟨2389,by decide⟩] | 3 => ![⟨2390,by decide⟩,⟨8,by decide⟩,⟨2390,by decide⟩] | 4 => ![⟨2391,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 5 => ![⟨2392,by decide⟩,⟨2376,by decide⟩,⟨1318,by decide⟩] | _ => ![⟨2393,by decide⟩,⟨2394,by decide⟩,⟨1368,by decide⟩]

def ntree11RRLLLLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2390,by decide⟩,⟨8,by decide⟩,⟨2395,by decide⟩] | 1 => ![⟨2396,by decide⟩,⟨10,by decide⟩,⟨2396,by decide⟩] | 2 => ![⟨2345,by decide⟩,⟨2394,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨2396,by decide⟩,⟨10,by decide⟩,⟨2397,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨2398,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨2399,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2400,by decide⟩] | _ => ![⟨1338,by decide⟩,⟨72,by decide⟩,⟨2401,by decide⟩]

def ntree11RRLLLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRLLLLLRL i else ntree11RRLLLLLRR (i - 7)

def ntree11RRLLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRLLLLLL i else ntree11RRLLLLLR (i - 15)

def ntree11RRLLLLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨27,by decide⟩,⟨27,by decide⟩,⟨2402,by decide⟩] | 1 => ![⟨2374,by decide⟩,⟨2403,by decide⟩,⟨2400,by decide⟩] | 2 => ![⟨27,by decide⟩,⟨2404,by decide⟩,⟨27,by decide⟩] | 3 => ![⟨2405,by decide⟩,⟨10,by decide⟩,⟨2405,by decide⟩] | 4 => ![⟨2405,by decide⟩,⟨10,by decide⟩,⟨2406,by decide⟩] | 5 => ![⟨2407,by decide⟩,⟨8,by decide⟩,⟨2407,by decide⟩] | _ => ![⟨2407,by decide⟩,⟨8,by decide⟩,⟨2408,by decide⟩]

def ntree11RRLLLLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨1490,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨61,by decide⟩,⟨2376,by decide⟩,⟨1378,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨2409,by decide⟩] | 3 => ![⟨2410,by decide⟩,⟨2410,by decide⟩,⟨79,by decide⟩] | 4 => ![⟨2411,by decide⟩,⟨2412,by decide⟩,⟨9,by decide⟩] | 5 => ![⟨2413,by decide⟩,⟨2413,by decide⟩,⟨85,by decide⟩] | 6 => ![⟨2411,by decide⟩,⟨2411,by decide⟩,⟨8,by decide⟩] | _ => ![⟨2414,by decide⟩,⟨2414,by decide⟩,⟨87,by decide⟩]

def ntree11RRLLLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRLLLLRLL i else ntree11RRLLLLRLR (i - 7)

def ntree11RRLLLLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2415,by decide⟩,⟨2416,by decide⟩,⟨18,by decide⟩] | 1 => ![⟨2415,by decide⟩,⟨2415,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨2417,by decide⟩,⟨79,by decide⟩,⟨2417,by decide⟩] | 3 => ![⟨2418,by decide⟩,⟨85,by decide⟩,⟨2418,by decide⟩] | 4 => ![⟨2419,by decide⟩,⟨2415,by decide⟩,⟨1322,by decide⟩] | 5 => ![⟨2420,by decide⟩,⟨87,by decide⟩,⟨2420,by decide⟩] | 6 => ![⟨2420,by decide⟩,⟨97,by decide⟩,⟨2421,by decide⟩] | _ => ![⟨2422,by decide⟩,⟨2413,by decide⟩,⟨2418,by decide⟩]

def ntree11RRLLLLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2423,by decide⟩,⟨83,by decide⟩,⟨2423,by decide⟩] | 1 => ![⟨2424,by decide⟩,⟨2411,by decide⟩,⟨2364,by decide⟩] | 2 => ![⟨2425,by decide⟩,⟨2426,by decide⟩,⟨80,by decide⟩] | 3 => ![⟨79,by decide⟩,⟨2427,by decide⟩,⟨79,by decide⟩] | 4 => ![⟨2428,by decide⟩,⟨2429,by decide⟩,⟨86,by decide⟩] | 5 => ![⟨2415,by decide⟩,⟨2430,by decide⟩,⟨11,by decide⟩] | 6 => ![⟨85,by decide⟩,⟨2431,by decide⟩,⟨85,by decide⟩] | _ => ![⟨2415,by decide⟩,⟨2432,by decide⟩,⟨10,by decide⟩]

def ntree11RRLLLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRLLLLRRL i else ntree11RRLLLLRRR (i - 8)

def ntree11RRLLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRLLLLRL i else ntree11RRLLLLRR (i - 15)

def ntree11RRLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 30 then ntree11RRLLLLL i else ntree11RRLLLLR (i - 30)

def ntree11RRLLLRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2425,by decide⟩,⟨2425,by decide⟩,⟨79,by decide⟩] | 1 => ![⟨2428,by decide⟩,⟨2428,by decide⟩,⟨85,by decide⟩] | 2 => ![⟨2433,by decide⟩,⟨2434,by decide⟩,⟨88,by decide⟩] | 3 => ![⟨87,by decide⟩,⟨2435,by decide⟩,⟨87,by decide⟩] | 4 => ![⟨2420,by decide⟩,⟨2435,by decide⟩,⟨2420,by decide⟩] | 5 => ![⟨2436,by decide⟩,⟨2428,by decide⟩,⟨2418,by decide⟩] | _ => ![⟨1380,by decide⟩,⟨2437,by decide⟩,⟨0,by decide⟩]

def ntree11RRLLLRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2410,by decide⟩,⟨2438,by decide⟩,⟨79,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨2439,by decide⟩,⟨8,by decide⟩] | 2 => ![⟨1389,by decide⟩,⟨2440,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨2413,by decide⟩,⟨2441,by decide⟩,⟨85,by decide⟩] | 4 => ![⟨2411,by decide⟩,⟨2442,by decide⟩,⟨8,by decide⟩] | 5 => ![⟨1391,by decide⟩,⟨2443,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨2414,by decide⟩,⟨2444,by decide⟩,⟨87,by decide⟩] | _ => ![⟨10,by decide⟩,⟨2376,by decide⟩,⟨10,by decide⟩]

def ntree11RRLLLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRLLLRLLL i else ntree11RRLLLRLLR (i - 7)

def ntree11RRLLLRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨87,by decide⟩,⟨87,by decide⟩,⟨2445,by decide⟩] | 1 => ![⟨2446,by decide⟩,⟨1389,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨2447,by decide⟩,⟨1388,by decide⟩,⟨2348,by decide⟩] | 3 => ![⟨1389,by decide⟩,⟨1389,by decide⟩,⟨2349,by decide⟩] | 4 => ![⟨85,by decide⟩,⟨85,by decide⟩,⟨2448,by decide⟩] | 5 => ![⟨2449,by decide⟩,⟨2412,by decide⟩,⟨2344,by decide⟩] | 6 => ![⟨2413,by decide⟩,⟨2413,by decide⟩,⟨2448,by decide⟩] | _ => ![⟨2411,by decide⟩,⟨2411,by decide⟩,⟨2346,by decide⟩]

def ntree11RRLLLRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨1398,by decide⟩,⟨2349,by decide⟩] | 1 => ![⟨2450,by decide⟩,⟨2416,by decide⟩,⟨2351,by decide⟩] | 2 => ![⟨2415,by decide⟩,⟨2415,by decide⟩,⟨2349,by decide⟩] | 3 => ![⟨2451,by decide⟩,⟨85,by decide⟩,⟨2451,by decide⟩] | 4 => ![⟨1460,by decide⟩,⟨35,by decide⟩,⟨2452,by decide⟩] | 5 => ![⟨2453,by decide⟩,⟨10,by decide⟩,⟨2453,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2349,by decide⟩] | _ => ![⟨2453,by decide⟩,⟨18,by decide⟩,⟨2454,by decide⟩]

def ntree11RRLLLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRLLLRLRL i else ntree11RRLLLRLRR (i - 8)

def ntree11RRLLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRLLLRLL i else ntree11RRLLLRLR (i - 15)

def ntree11RRLLLRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1389,by decide⟩,⟨2455,by decide⟩,⟨35,by decide⟩] | 1 => ![⟨2456,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | 2 => ![⟨2457,by decide⟩,⟨1414,by decide⟩,⟨2349,by decide⟩] | 3 => ![⟨2458,by decide⟩,⟨86,by decide⟩,⟨2459,by decide⟩] | 4 => ![⟨2460,by decide⟩,⟨11,by decide⟩,⟨2461,by decide⟩] | 5 => ![⟨2458,by decide⟩,⟨85,by decide⟩,⟨2458,by decide⟩] | _ => ![⟨2462,by decide⟩,⟨2429,by decide⟩,⟨2459,by decide⟩]

def ntree11RRLLLRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2463,by decide⟩,⟨2373,by decide⟩,⟨2461,by decide⟩] | 1 => ![⟨2464,by decide⟩,⟨2430,by decide⟩,⟨2348,by decide⟩] | 2 => ![⟨2458,by decide⟩,⟨2431,by decide⟩,⟨2458,by decide⟩] | 3 => ![⟨2465,by decide⟩,⟨2432,by decide⟩,⟨2377,by decide⟩] | 4 => ![⟨85,by decide⟩,⟨85,by decide⟩,⟨2466,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2467,by decide⟩] | 6 => ![⟨2428,by decide⟩,⟨2428,by decide⟩,⟨2466,by decide⟩] | _ => ![⟨2375,by decide⟩,⟨2375,by decide⟩,⟨2467,by decide⟩]

def ntree11RRLLLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRLLLRRLL i else ntree11RRLLLRRLR (i - 7)

def ntree11RRLLLRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2460,by decide⟩,⟨10,by decide⟩,⟨2460,by decide⟩] | 1 => ![⟨2460,by decide⟩,⟨2376,by decide⟩,⟨2460,by decide⟩] | 2 => ![⟨2453,by decide⟩,⟨2376,by decide⟩,⟨2453,by decide⟩] | 3 => ![⟨2468,by decide⟩,⟨2469,by decide⟩,⟨2453,by decide⟩] | 4 => ![⟨2470,by decide⟩,⟨2471,by decide⟩,⟨2349,by decide⟩] | 5 => ![⟨2472,by decide⟩,⟨142,by decide⟩,⟨2472,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨1477,by decide⟩,⟨10,by decide⟩] | _ => ![⟨2469,by decide⟩,⟨2469,by decide⟩,⟨10,by decide⟩]

def ntree11RRLLLRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨2471,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨2396,by decide⟩,⟨1414,by decide⟩,⟨2396,by decide⟩] | 2 => ![⟨2473,by decide⟩,⟨1429,by decide⟩,⟨2397,by decide⟩] | 3 => ![⟨2460,by decide⟩,⟨10,by decide⟩,⟨2474,by decide⟩] | 4 => ![⟨2458,by decide⟩,⟨85,by decide⟩,⟨2475,by decide⟩] | 5 => ![⟨2390,by decide⟩,⟨2439,by decide⟩,⟨2390,by decide⟩] | 6 => ![⟨2476,by decide⟩,⟨2440,by decide⟩,⟨2474,by decide⟩] | _ => ![⟨2477,by decide⟩,⟨83,by decide⟩,⟨83,by decide⟩]

def ntree11RRLLLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRLLLRRRL i else ntree11RRLLLRRRR (i - 8)

def ntree11RRLLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRLLLRRL i else ntree11RRLLLRRR (i - 15)

def ntree11RRLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RRLLLRL i else ntree11RRLLLRR (i - 31)

def ntree11RRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 61 then ntree11RRLLLL i else ntree11RRLLLR (i - 61)

def ntree11RRLLRLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2478,by decide⟩,⟨2441,by decide⟩,⟨2475,by decide⟩] | 1 => ![⟨2479,by decide⟩,⟨2442,by decide⟩,⟨2395,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2480,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨1490,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨2336,by decide⟩,⟨0,by decide⟩,⟨2336,by decide⟩] | 5 => ![⟨2340,by decide⟩,⟨4,by decide⟩,⟨2340,by decide⟩] | _ => ![⟨2343,by decide⟩,⟨8,by decide⟩,⟨2343,by decide⟩]

def ntree11RRLLRLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2481,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2482,by decide⟩] | 2 => ![⟨2347,by decide⟩,⟨10,by decide⟩,⟨2347,by decide⟩] | 3 => ![⟨2483,by decide⟩,⟨2483,by decide⟩,⟨2482,by decide⟩] | 4 => ![⟨2483,by decide⟩,⟨2483,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨2484,by decide⟩] | 6 => ![⟨1317,by decide⟩,⟨10,by decide⟩,⟨2485,by decide⟩] | _ => ![⟨1310,by decide⟩,⟨160,by decide⟩,⟨2486,by decide⟩]

def ntree11RRLLRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRLLRLLLL i else ntree11RRLLRLLLR (i - 7)

def ntree11RRLLRLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1317,by decide⟩,⟨166,by decide⟩,⟨2487,by decide⟩] | 1 => ![⟨1322,by decide⟩,⟨173,by decide⟩,⟨2488,by decide⟩] | 2 => ![⟨1327,by decide⟩,⟨176,by decide⟩,⟨2489,by decide⟩] | 3 => ![⟨2356,by decide⟩,⟨10,by decide⟩,⟨2356,by decide⟩] | 4 => ![⟨1330,by decide⟩,⟨173,by decide⟩,⟨2490,by decide⟩] | 5 => ![⟨2359,by decide⟩,⟨8,by decide⟩,⟨2359,by decide⟩] | 6 => ![⟨2364,by decide⟩,⟨184,by decide⟩,⟨2491,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree11RRLLRLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨2492,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨2493,by decide⟩,⟨2493,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨2493,by decide⟩,⟨2493,by decide⟩,⟨2482,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨2376,by decide⟩,⟨2482,by decide⟩] | _ => ![⟨2494,by decide⟩,⟨2493,by decide⟩,⟨2347,by decide⟩]

def ntree11RRLLRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRLLRLLRL i else ntree11RRLLRLLRR (i - 8)

def ntree11RRLLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRLLRLLL i else ntree11RRLLRLLR (i - 15)

def ntree11RRLLRLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1338,by decide⟩,⟨194,by decide⟩,⟨2495,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨2496,by decide⟩,⟨160,by decide⟩] | 2 => ![⟨1335,by decide⟩,⟨160,by decide⟩,⟨2497,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨2498,by decide⟩,⟨166,by decide⟩] | 4 => ![⟨1533,by decide⟩,⟨2498,by decide⟩,⟨2499,by decide⟩] | 5 => ![⟨1320,by decide⟩,⟨189,by decide⟩,⟨2500,by decide⟩] | _ => ![⟨1322,by decide⟩,⟨191,by decide⟩,⟨2501,by decide⟩]

def ntree11RRLLRLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1322,by decide⟩,⟨2502,by decide⟩,⟨2488,by decide⟩] | 1 => ![⟨1350,by decide⟩,⟨208,by decide⟩,⟨2503,by decide⟩] | 2 => ![⟨2504,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨2504,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨2502,by decide⟩,⟨173,by decide⟩] | 5 => ![⟨2505,by decide⟩,⟨10,by decide⟩,⟨2356,by decide⟩] | 6 => ![⟨1354,by decide⟩,⟨173,by decide⟩,⟨2506,by decide⟩] | _ => ![⟨167,by decide⟩,⟨2376,by decide⟩,⟨2507,by decide⟩]

def ntree11RRLLRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRLLRLRLL i else ntree11RRLLRLRLR (i - 7)

def ntree11RRLLRLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1322,by decide⟩,⟨2508,by decide⟩,⟨1322,by decide⟩] | 1 => ![⟨2509,by decide⟩,⟨2483,by decide⟩,⟨2396,by decide⟩] | 2 => ![⟨1502,by decide⟩,⟨2510,by decide⟩,⟨220,by decide⟩] | 3 => ![⟨1335,by decide⟩,⟨220,by decide⟩,⟨2511,by decide⟩] | 4 => ![⟨1547,by decide⟩,⟨2512,by decide⟩,⟨2513,by decide⟩] | 5 => ![⟨226,by decide⟩,⟨2376,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨2514,by decide⟩,⟨10,by decide⟩] | _ => ![⟨10,by decide⟩,⟨2515,by decide⟩,⟨10,by decide⟩]

def ntree11RRLLRLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1514,by decide⟩,⟨2516,by decide⟩,⟨229,by decide⟩] | 1 => ![⟨1338,by decide⟩,⟨229,by decide⟩,⟨2517,by decide⟩] | 2 => ![⟨27,by decide⟩,⟨27,by decide⟩,⟨2518,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨2519,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨2504,by decide⟩,⟨229,by decide⟩,⟨229,by decide⟩] | 5 => ![⟨2520,by decide⟩,⟨1514,by decide⟩,⟨2405,by decide⟩] | 6 => ![⟨1354,by decide⟩,⟨229,by decide⟩,⟨2521,by decide⟩] | _ => ![⟨2522,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩]

def ntree11RRLLRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRLLRLRRL i else ntree11RRLLRLRRR (i - 8)

def ntree11RRLLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRLLRLRL i else ntree11RRLLRLRR (i - 15)

def ntree11RRLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RRLLRLL i else ntree11RRLLRLR (i - 31)

def ntree11RRLLRRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨2508,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨2523,by decide⟩,⟨8,by decide⟩] | 2 => ![⟨2524,by decide⟩,⟨2524,by decide⟩,⟨87,by decide⟩] | 3 => ![⟨2525,by decide⟩,⟨2525,by decide⟩,⟨8,by decide⟩] | 4 => ![⟨2526,by decide⟩,⟨2526,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨245,by decide⟩,⟨1398,by decide⟩,⟨10,by decide⟩] | _ => ![⟨2527,by decide⟩,⟨2526,by decide⟩,⟨1322,by decide⟩]

def ntree11RRLLRRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2528,by decide⟩,⟨2525,by decide⟩,⟨2364,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨2529,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨2530,by decide⟩,⟨2530,by decide⟩,⟨87,by decide⟩] | 3 => ![⟨2493,by decide⟩,⟨2531,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1577,by decide⟩,⟨1577,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨2526,by decide⟩,⟨2532,by decide⟩,⟨270,by decide⟩] | 6 => ![⟨79,by decide⟩,⟨79,by decide⟩,⟨2533,by decide⟩] | _ => ![⟨245,by decide⟩,⟨2376,by decide⟩,⟨1579,by decide⟩]

def ntree11RRLLRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRLLRRLLL i else ntree11RRLLRRLLR (i - 7)

def ntree11RRLLRRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨246,by decide⟩,⟨2431,by decide⟩,⟨2534,by decide⟩] | 1 => ![⟨2417,by decide⟩,⟨269,by decide⟩,⟨2535,by decide⟩] | 2 => ![⟨2418,by decide⟩,⟨271,by decide⟩,⟨2536,by decide⟩] | 3 => ![⟨2420,by decide⟩,⟨272,by decide⟩,⟨2537,by decide⟩] | 4 => ![⟨2527,by decide⟩,⟨2532,by decide⟩,⟨1584,by decide⟩] | 5 => ![⟨2538,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | 6 => ![⟨2504,by decide⟩,⟨1414,by decide⟩,⟨10,by decide⟩] | _ => ![⟨85,by decide⟩,⟨85,by decide⟩,⟨2534,by decide⟩]

def ntree11RRLLRRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2539,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨2504,by decide⟩,⟨2529,by decide⟩,⟨1579,by decide⟩] | 2 => ![⟨2540,by decide⟩,⟨1577,by decide⟩,⟨1322,by decide⟩] | 3 => ![⟨2483,by decide⟩,⟨2541,by decide⟩,⟨293,by decide⟩] | 4 => ![⟨299,by decide⟩,⟨2431,by decide⟩,⟨85,by decide⟩] | 5 => ![⟨304,by decide⟩,⟨2376,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨2542,by decide⟩,⟨83,by decide⟩,⟨83,by decide⟩] | _ => ![⟨2522,by decide⟩,⟨2439,by decide⟩,⟨8,by decide⟩]

def ntree11RRLLRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRLLRRLRL i else ntree11RRLLRRLRR (i - 8)

def ntree11RRLLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRLLRRLL i else ntree11RRLLRRLR (i - 15)

def ntree11RRLLRRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2543,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨2544,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 2 => ![⟨2347,by decide⟩,⟨1398,by decide⟩,⟨2347,by decide⟩] | 3 => ![⟨2343,by decide⟩,⟨2523,by decide⟩,⟨2343,by decide⟩] | 4 => ![⟨2545,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | 5 => ![⟨2546,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨2547,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11RRLLRRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2548,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨2549,by decide⟩] | 2 => ![⟨2550,by decide⟩,⟨2526,by decide⟩,⟨1317,by decide⟩] | 3 => ![⟨2525,by decide⟩,⟨2525,by decide⟩,⟨2549,by decide⟩] | 4 => ![⟨2526,by decide⟩,⟨2526,by decide⟩,⟨1608,by decide⟩] | 5 => ![⟨2551,by decide⟩,⟨2551,by decide⟩,⟨85,by decide⟩] | 6 => ![⟨2552,by decide⟩,⟨2553,by decide⟩,⟨173,by decide⟩] | _ => ![⟨1317,by decide⟩,⟨173,by decide⟩,⟨2554,by decide⟩]

def ntree11RRLLRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRLLRRRLL i else ntree11RRLLRRRLR (i - 7)

def ntree11RRLLRRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2555,by decide⟩,⟨2551,by decide⟩,⟨2451,by decide⟩] | 1 => ![⟨2556,by decide⟩,⟨2552,by decide⟩,⟨1460,by decide⟩] | 2 => ![⟨2557,by decide⟩,⟨1514,by decide⟩,⟨2453,by decide⟩] | 3 => ![⟨2558,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩] | 4 => ![⟨2453,by decide⟩,⟨173,by decide⟩,⟨2559,by decide⟩] | 5 => ![⟨2552,by decide⟩,⟨2552,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨1559,by decide⟩,⟨2560,by decide⟩,⟨173,by decide⟩] | _ => ![⟨2347,by decide⟩,⟨2529,by decide⟩,⟨2347,by decide⟩]

def ntree11RRLLRRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨2376,by decide⟩,⟨1608,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2561,by decide⟩] | 3 => ![⟨1338,by decide⟩,⟨10,by decide⟩,⟨2562,by decide⟩] | 4 => ![⟨2347,by decide⟩,⟨270,by decide⟩,⟨2563,by decide⟩] | 5 => ![⟨1577,by decide⟩,⟨1577,by decide⟩,⟨2561,by decide⟩] | 6 => ![⟨2526,by decide⟩,⟨2526,by decide⟩,⟨2561,by decide⟩] | _ => ![⟨2564,by decide⟩,⟨2532,by decide⟩,⟨1622,by decide⟩]

def ntree11RRLLRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRLLRRRRL i else ntree11RRLLRRRRR (i - 8)

def ntree11RRLLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRLLRRRL i else ntree11RRLLRRRR (i - 15)

def ntree11RRLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RRLLRRL i else ntree11RRLLRRR (i - 31)

def ntree11RRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11RRLLRL i else ntree11RRLLRR (i - 62)

def ntree11RRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 123 then ntree11RRLLL i else ntree11RRLLR (i - 123)

def ntree11RRLRLLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨85,by decide⟩,⟨2565,by decide⟩,⟨317,by decide⟩] | 1 => ![⟨2460,by decide⟩,⟨173,by decide⟩,⟨2566,by decide⟩] | 2 => ![⟨2458,by decide⟩,⟨317,by decide⟩,⟨2567,by decide⟩] | 3 => ![⟨2451,by decide⟩,⟨271,by decide⟩,⟨2568,by decide⟩] | 4 => ![⟨2453,by decide⟩,⟨2502,by decide⟩,⟨2559,by decide⟩] | 5 => ![⟨2472,by decide⟩,⟨344,by decide⟩,⟨2569,by decide⟩] | _ => ![⟨2396,by decide⟩,⟨293,by decide⟩,⟨2570,by decide⟩]

def ntree11RRLRLLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2390,by decide⟩,⟨291,by decide⟩,⟨2571,by decide⟩] | 1 => ![⟨2551,by decide⟩,⟨2572,by decide⟩,⟨348,by decide⟩] | 2 => ![⟨2552,by decide⟩,⟨2573,by decide⟩,⟨350,by decide⟩] | 3 => ![⟨2458,by decide⟩,⟨348,by decide⟩,⟨2574,by decide⟩] | 4 => ![⟨2460,by decide⟩,⟨350,by decide⟩,⟨2575,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨2576,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨2577,by decide⟩,⟨358,by decide⟩,⟨2578,by decide⟩] | _ => ![⟨357,by decide⟩,⟨357,by decide⟩,⟨2579,by decide⟩]

def ntree11RRLRLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRLRLLLLL i else ntree11RRLRLLLLR (i - 7)

def ntree11RRLRLLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2580,by decide⟩,⟨10,by decide⟩,⟨2580,by decide⟩] | 1 => ![⟨2581,by decide⟩,⟨357,by decide⟩,⟨2581,by decide⟩] | 2 => ![⟨2580,by decide⟩,⟨10,by decide⟩,⟨2582,by decide⟩] | 3 => ![⟨2583,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1647,by decide⟩,⟨10,by decide⟩,⟨1647,by decide⟩] | 5 => ![⟨2580,by decide⟩,⟨11,by decide⟩,⟨2584,by decide⟩] | 6 => ![⟨2345,by decide⟩,⟨2345,by decide⟩,⟨2482,by decide⟩] | _ => ![⟨2483,by decide⟩,⟨2483,by decide⟩,⟨2349,by decide⟩]

def ntree11RRLRLLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨364,by decide⟩,⟨364,by decide⟩] | 1 => ![⟨370,by decide⟩,⟨367,by decide⟩,⟨367,by decide⟩] | 2 => ![⟨1330,by decide⟩,⟨364,by decide⟩,⟨2585,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨2586,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨370,by decide⟩,⟨370,by decide⟩,⟨370,by decide⟩] | 5 => ![⟨167,by decide⟩,⟨2587,by decide⟩,⟨2349,by decide⟩] | 6 => ![⟨1650,by decide⟩,⟨370,by decide⟩,⟨1650,by decide⟩] | _ => ![⟨2345,by decide⟩,⟨2588,by decide⟩,⟨173,by decide⟩]

def ntree11RRLRLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRLRLLLRL i else ntree11RRLRLLLRR (i - 8)

def ntree11RRLRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRLRLLLL i else ntree11RRLRLLLR (i - 15)

def ntree11RRLRLLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2589,by decide⟩,⟨377,by decide⟩,⟨2590,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨173,by decide⟩,⟨2591,by decide⟩] | 2 => ![⟨2592,by decide⟩,⟨2345,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨2593,by decide⟩,⟨376,by decide⟩,⟨2593,by decide⟩] | 4 => ![⟨2593,by decide⟩,⟨385,by decide⟩,⟨2594,by decide⟩] | 5 => ![⟨2593,by decide⟩,⟨377,by decide⟩,⟨2595,by decide⟩] | _ => ![⟨2363,by decide⟩,⟨2588,by decide⟩,⟨2488,by decide⟩]

def ntree11RRLRLLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1354,by decide⟩,⟨10,by decide⟩,⟨2596,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨2597,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨2580,by decide⟩,⟨2597,by decide⟩,⟨2580,by decide⟩] | 3 => ![⟨2598,by decide⟩,⟨2375,by decide⟩,⟨2580,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨2597,by decide⟩,⟨2349,by decide⟩] | 5 => ![⟨2599,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨2493,by decide⟩,⟨2600,by decide⟩,⟨11,by decide⟩] | _ => ![⟨2601,by decide⟩,⟨2600,by decide⟩,⟨2584,by decide⟩]

def ntree11RRLRLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRLRLLRLL i else ntree11RRLRLLRLR (i - 7)

def ntree11RRLRLLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2598,by decide⟩,⟨2373,by decide⟩,⟨2584,by decide⟩] | 1 => ![⟨2494,by decide⟩,⟨2600,by decide⟩,⟨2348,by decide⟩] | 2 => ![⟨2374,by decide⟩,⟨2597,by decide⟩,⟨2482,by decide⟩] | 3 => ![⟨2374,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2349,by decide⟩] | 5 => ![⟨391,by decide⟩,⟨395,by decide⟩,⟨395,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨2587,by decide⟩,⟨10,by decide⟩] | _ => ![⟨2602,by decide⟩,⟨391,by decide⟩,⟨391,by decide⟩]

def ntree11RRLRLLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨167,by decide⟩,⟨2587,by decide⟩,⟨2349,by decide⟩] | 1 => ![⟨1322,by decide⟩,⟨2597,by decide⟩,⟨1322,by decide⟩] | 2 => ![⟨1322,by decide⟩,⟨2603,by decide⟩,⟨2353,by decide⟩] | 3 => ![⟨2378,by decide⟩,⟨2604,by decide⟩,⟨2488,by decide⟩] | 4 => ![⟨2605,by decide⟩,⟨2606,by decide⟩,⟨377,by decide⟩] | 5 => ![⟨2607,by decide⟩,⟨2605,by decide⟩,⟨2593,by decide⟩] | 6 => ![⟨2607,by decide⟩,⟨2606,by decide⟩,⟨2595,by decide⟩] | _ => ![⟨2608,by decide⟩,⟨357,by decide⟩,⟨2608,by decide⟩]

def ntree11RRLRLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRLRLLRRL i else ntree11RRLRLLRRR (i - 8)

def ntree11RRLRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRLRLLRL i else ntree11RRLRLLRR (i - 15)

def ntree11RRLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RRLRLLL i else ntree11RRLRLLR (i - 31)

def ntree11RRLRLRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2608,by decide⟩,⟨357,by decide⟩,⟨2609,by decide⟩] | 1 => ![⟨2610,by decide⟩,⟨2597,by decide⟩,⟨2610,by decide⟩] | 2 => ![⟨2610,by decide⟩,⟨10,by decide⟩,⟨2610,by decide⟩] | 3 => ![⟨2611,by decide⟩,⟨2345,by decide⟩,⟨2610,by decide⟩] | 4 => ![⟨2612,by decide⟩,⟨357,by decide⟩,⟨2612,by decide⟩] | 5 => ![⟨2610,by decide⟩,⟨191,by decide⟩,⟨2613,by decide⟩] | _ => ![⟨10,by decide⟩,⟨1662,by decide⟩,⟨2349,by decide⟩]

def ntree11RRLRLRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2345,by decide⟩,⟨2614,by decide⟩,⟨191,by decide⟩] | 1 => ![⟨2610,by decide⟩,⟨2376,by decide⟩,⟨2610,by decide⟩] | 2 => ![⟨2396,by decide⟩,⟨2597,by decide⟩,⟨2396,by decide⟩] | 3 => ![⟨2615,by decide⟩,⟨2616,by decide⟩,⟨2617,by decide⟩] | 4 => ![⟨2611,by decide⟩,⟨2394,by decide⟩,⟨2617,by decide⟩] | 5 => ![⟨2509,by decide⟩,⟨2616,by decide⟩,⟨2397,by decide⟩] | 6 => ![⟨2610,by decide⟩,⟨10,by decide⟩,⟨2617,by decide⟩] | _ => ![⟨2618,by decide⟩,⟨370,by decide⟩,⟨370,by decide⟩]

def ntree11RRLRLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRLRLRLLL i else ntree11RRLRLRLLR (i - 7)

def ntree11RRLRLRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨226,by decide⟩,⟨10,by decide⟩,⟨2349,by decide⟩] | 1 => ![⟨1514,by decide⟩,⟨2619,by decide⟩,⟨72,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨2620,by decide⟩,⟨229,by decide⟩] | 3 => ![⟨376,by decide⟩,⟨2621,by decide⟩,⟨376,by decide⟩] | 4 => ![⟨376,by decide⟩,⟨376,by decide⟩,⟨2622,by decide⟩] | 5 => ![⟨2623,by decide⟩,⟨1514,by decide⟩,⟨2610,by decide⟩] | 6 => ![⟨2610,by decide⟩,⟨65,by decide⟩,⟨2624,by decide⟩] | _ => ![⟨61,by decide⟩,⟨1662,by decide⟩,⟨10,by decide⟩]

def ntree11RRLRLRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2610,by decide⟩,⟨229,by decide⟩,⟨2625,by decide⟩] | 1 => ![⟨2623,by decide⟩,⟨2516,by decide⟩,⟨2625,by decide⟩] | 2 => ![⟨376,by decide⟩,⟨376,by decide⟩,⟨2626,by decide⟩] | 3 => ![⟨405,by decide⟩,⟨2621,by decide⟩,⟨2626,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨2627,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1389,by decide⟩,⟨2628,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨2526,by decide⟩,⟨2629,by decide⟩,⟨11,by decide⟩] | _ => ![⟨2630,by decide⟩,⟨2630,by decide⟩,⟨10,by decide⟩]

def ntree11RRLRLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRLRLRLRL i else ntree11RRLRLRLRR (i - 8)

def ntree11RRLRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRLRLRLL i else ntree11RRLRLRLR (i - 15)

def ntree11RRLRLRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨85,by decide⟩,⟨433,by decide⟩,⟨433,by decide⟩] | 1 => ![⟨1322,by decide⟩,⟨438,by decide⟩,⟨2631,by decide⟩] | 2 => ![⟨2632,by decide⟩,⟨1388,by decide⟩,⟨11,by decide⟩] | 3 => ![⟨2633,by decide⟩,⟨2413,by decide⟩,⟨85,by decide⟩] | 4 => ![⟨1322,by decide⟩,⟨2627,by decide⟩,⟨1322,by decide⟩] | 5 => ![⟨1402,by decide⟩,⟨2628,by decide⟩,⟨1322,by decide⟩] | _ => ![⟨2527,by decide⟩,⟨2629,by decide⟩,⟨1334,by decide⟩]

def ntree11RRLRLRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2634,by decide⟩,⟨2630,by decide⟩,⟨1322,by decide⟩] | 1 => ![⟨85,by decide⟩,⟨2635,by decide⟩,⟨85,by decide⟩] | 2 => ![⟨1411,by decide⟩,⟨2636,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨2375,by decide⟩,⟨2637,by decide⟩,⟨270,by decide⟩] | 4 => ![⟨2638,by decide⟩,⟨2639,by decide⟩,⟨449,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨1414,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨2418,by decide⟩,⟨2635,by decide⟩,⟨2418,by decide⟩] | _ => ![⟨2640,by decide⟩,⟨2373,by decide⟩,⟨1699,by decide⟩]

def ntree11RRLRLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRLRLRRLL i else ntree11RRLRLRRLR (i - 7)

def ntree11RRLRLRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2384,by decide⟩,⟨2637,by decide⟩,⟨1584,by decide⟩] | 1 => ![⟨2641,by decide⟩,⟨2639,by decide⟩,⟨1707,by decide⟩] | 2 => ![⟨1389,by decide⟩,⟨2642,by decide⟩,⟨457,by decide⟩] | 3 => ![⟨85,by decide⟩,⟨2643,by decide⟩,⟨85,by decide⟩] | 4 => ![⟨2413,by decide⟩,⟨2644,by decide⟩,⟨271,by decide⟩] | 5 => ![⟨2483,by decide⟩,⟨2616,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨2645,by decide⟩,⟨10,by decide⟩] | _ => ![⟨10,by decide⟩,⟨2646,by decide⟩,⟨10,by decide⟩]

def ntree11RRLRLRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2526,by decide⟩,⟨2647,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨2630,by decide⟩,⟨2648,by decide⟩,⟨270,by decide⟩] | 2 => ![⟨2649,by decide⟩,⟨10,by decide⟩,⟨2650,by decide⟩] | 3 => ![⟨2651,by decide⟩,⟨10,by decide⟩,⟨2652,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨2597,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2653,by decide⟩] | 6 => ![⟨2654,by decide⟩,⟨2440,by decide⟩,⟨1718,by decide⟩] | _ => ![⟨117,by decide⟩,⟨2643,by decide⟩,⟨85,by decide⟩]

def ntree11RRLRLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRLRLRRRL i else ntree11RRLRLRRRR (i - 8)

def ntree11RRLRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRLRLRRL i else ntree11RRLRLRRR (i - 15)

def ntree11RRLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RRLRLRL i else ntree11RRLRLRR (i - 31)

def ntree11RRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11RRLRLL i else ntree11RRLRLR (i - 62)

def ntree11RRLRRLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨1662,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨2446,by decide⟩,⟨1714,by decide⟩,⟨270,by decide⟩] | 2 => ![⟨304,by decide⟩,⟨2645,by decide⟩,⟨1378,by decide⟩] | 3 => ![⟨464,by decide⟩,⟨2646,by decide⟩,⟨1378,by decide⟩] | 4 => ![⟨2526,by decide⟩,⟨2526,by decide⟩,⟨1378,by decide⟩] | 5 => ![⟨2655,by decide⟩,⟨2532,by decide⟩,⟨1729,by decide⟩] | _ => ![⟨1647,by decide⟩,⟨2627,by decide⟩,⟨1647,by decide⟩]

def ntree11RRLRRLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2656,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2657,by decide⟩] | 2 => ![⟨2526,by decide⟩,⟨2526,by decide⟩,⟨2656,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨318,by decide⟩,⟨2658,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2659,by decide⟩] | 6 => ![⟨2551,by decide⟩,⟨2660,by decide⟩,⟨86,by decide⟩] | _ => ![⟨2661,by decide⟩,⟨2662,by decide⟩,⟨377,by decide⟩]

def ntree11RRLRRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRLRRLLLL i else ntree11RRLRRLLLR (i - 7)

def ntree11RRLRRLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2413,by decide⟩,⟨2663,by decide⟩,⟨317,by decide⟩] | 1 => ![⟨2661,by decide⟩,⟨2661,by decide⟩,⟨376,by decide⟩] | 2 => ![⟨2664,by decide⟩,⟨85,by decide⟩,⟨2664,by decide⟩] | 3 => ![⟨2665,by decide⟩,⟨10,by decide⟩,⟨2665,by decide⟩] | 4 => ![⟨2665,by decide⟩,⟨270,by decide⟩,⟨2666,by decide⟩] | 5 => ![⟨2667,by decide⟩,⟨1411,by decide⟩,⟨2665,by decide⟩] | 6 => ![⟨2665,by decide⟩,⟨2627,by decide⟩,⟨2665,by decide⟩] | _ => ![⟨2665,by decide⟩,⟨11,by decide⟩,⟨2668,by decide⟩]

def ntree11RRLRRLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2669,by decide⟩,⟨449,by decide⟩,⟨2670,by decide⟩] | 1 => ![⟨2671,by decide⟩,⟨2629,by decide⟩,⟨2668,by decide⟩] | 2 => ![⟨2671,by decide⟩,⟨2526,by decide⟩,⟨2665,by decide⟩] | 3 => ![⟨2456,by decide⟩,⟨317,by decide⟩,⟨317,by decide⟩] | 4 => ![⟨2457,by decide⟩,⟨1624,by decide⟩,⟨2658,by decide⟩] | 5 => ![⟨2665,by decide⟩,⟨173,by decide⟩,⟨2672,by decide⟩] | 6 => ![⟨2605,by decide⟩,⟨2605,by decide⟩,⟨376,by decide⟩] | _ => ![⟨2664,by decide⟩,⟨2643,by decide⟩,⟨2664,by decide⟩]

def ntree11RRLRRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRLRRLLRL i else ntree11RRLRRLLRR (i - 8)

def ntree11RRLRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRLRRLLL i else ntree11RRLRRLLR (i - 15)

def ntree11RRLRRLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2665,by decide⟩,⟨1662,by decide⟩,⟨2665,by decide⟩] | 1 => ![⟨2673,by decide⟩,⟨1714,by decide⟩,⟨2666,by decide⟩] | 2 => ![⟨2674,by decide⟩,⟨10,by decide⟩,⟨2674,by decide⟩] | 3 => ![⟨2665,by decide⟩,⟨10,by decide⟩,⟨2675,by decide⟩] | 4 => ![⟨2674,by decide⟩,⟨270,by decide⟩,⟨2676,by decide⟩] | 5 => ![⟨2665,by decide⟩,⟨2645,by decide⟩,⟨2665,by decide⟩] | _ => ![⟨2671,by decide⟩,⟨2647,by decide⟩,⟨2675,by decide⟩]

def ntree11RRLRRLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2374,by decide⟩,⟨350,by decide⟩,⟨350,by decide⟩] | 1 => ![⟨2677,by decide⟩,⟨350,by decide⟩,⟨2678,by decide⟩] | 2 => ![⟨2679,by decide⟩,⟨350,by decide⟩,⟨2678,by decide⟩] | 3 => ![⟨2665,by decide⟩,⟨229,by decide⟩,⟨2680,by decide⟩] | 4 => ![⟨2661,by decide⟩,⟨2681,by decide⟩,⟨495,by decide⟩] | 5 => ![⟨1746,by decide⟩,⟨500,by decide⟩,⟨2682,by decide⟩] | 6 => ![⟨2683,by decide⟩,⟨8,by decide⟩,⟨2683,by decide⟩] | _ => ![⟨2683,by decide⟩,⟨504,by decide⟩,⟨2684,by decide⟩]

def ntree11RRLRRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRLRRLRLL i else ntree11RRLRRLRLR (i - 7)

def ntree11RRLRRLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1748,by decide⟩,⟨510,by decide⟩,⟨2685,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨1318,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨2686,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨2687,by decide⟩] | 4 => ![⟨512,by decide⟩,⟨512,by decide⟩,⟨2688,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨2689,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2690,by decide⟩] | _ => ![⟨514,by decide⟩,⟨514,by decide⟩,⟨2691,by decide⟩]

def ntree11RRLRRLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1320,by decide⟩,⟨500,by decide⟩,⟨2692,by decide⟩] | 1 => ![⟨1754,by decide⟩,⟨516,by decide⟩,⟨2693,by decide⟩] | 2 => ![⟨1322,by decide⟩,⟨510,by decide⟩,⟨2694,by decide⟩] | 3 => ![⟨1756,by decide⟩,⟨517,by decide⟩,⟨2695,by decide⟩] | 4 => ![⟨1322,by decide⟩,⟨2689,by decide⟩,⟨1322,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2696,by decide⟩] | 6 => ![⟨514,by decide⟩,⟨514,by decide⟩,⟨2697,by decide⟩] | _ => ![⟨8,by decide⟩,⟨2698,by decide⟩,⟨8,by decide⟩]

def ntree11RRLRRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRLRRLRRL i else ntree11RRLRRLRRR (i - 8)

def ntree11RRLRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRLRRLRL i else ntree11RRLRRLRR (i - 15)

def ntree11RRLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RRLRRLL i else ntree11RRLRRLR (i - 31)

def ntree11RRLRRRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨2689,by decide⟩,⟨1331,by decide⟩] | 1 => ![⟨1322,by decide⟩,⟨523,by decide⟩,⟨2699,by decide⟩] | 2 => ![⟨1756,by decide⟩,⟨524,by decide⟩,⟨2700,by decide⟩] | 3 => ![⟨2701,by decide⟩,⟨521,by decide⟩,⟨2701,by decide⟩] | 4 => ![⟨2364,by decide⟩,⟨2698,by decide⟩,⟨2364,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨2376,by decide⟩,⟨1344,by decide⟩] | _ => ![⟨0,by decide⟩,⟨526,by decide⟩,⟨2702,by decide⟩]

def ntree11RRLRRRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2703,by decide⟩,⟨529,by decide⟩,⟨2704,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨529,by decide⟩,⟨2705,by decide⟩] | 2 => ![⟨2703,by decide⟩,⟨506,by decide⟩,⟨2706,by decide⟩] | 3 => ![⟨2374,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | 4 => ![⟨10,by decide⟩,⟨2376,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨2707,by decide⟩,⟨2708,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | _ => ![⟨2374,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩]

def ntree11RRLRRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRLRRRLLL i else ntree11RRLRRRLLR (i - 7)

def ntree11RRLRRRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2709,by decide⟩,⟨2710,by decide⟩,⟨506,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨2711,by decide⟩] | 2 => ![⟨2369,by decide⟩,⟨2686,by decide⟩,⟨2711,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨2712,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨2713,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2714,by decide⟩] | 6 => ![⟨2374,by decide⟩,⟨2689,by decide⟩,⟨2714,by decide⟩] | _ => ![⟨10,by decide⟩,⟨2715,by decide⟩,⟨10,by decide⟩]

def ntree11RRLRRRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2716,by decide⟩] | 1 => ![⟨1320,by decide⟩,⟨526,by decide⟩,⟨2717,by decide⟩] | 2 => ![⟨1320,by decide⟩,⟨534,by decide⟩,⟨2718,by decide⟩] | 3 => ![⟨1322,by decide⟩,⟨529,by decide⟩,⟨2719,by decide⟩] | 4 => ![⟨1322,by decide⟩,⟨535,by decide⟩,⟨2720,by decide⟩] | 5 => ![⟨2378,by decide⟩,⟨2721,by decide⟩,⟨2719,by decide⟩] | 6 => ![⟨1322,by decide⟩,⟨2715,by decide⟩,⟨1322,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2722,by decide⟩]

def ntree11RRLRRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRLRRRLRL i else ntree11RRLRRRLRR (i - 8)

def ntree11RRLRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRLRRRLL i else ntree11RRLRRRLR (i - 15)

def ntree11RRLRRRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2382,by decide⟩,⟨2689,by decide⟩,⟨2722,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2723,by decide⟩] | 2 => ![⟨869,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1322,by decide⟩,⟨544,by decide⟩,⟨2724,by decide⟩] | 4 => ![⟨1322,by decide⟩,⟨546,by decide⟩,⟨2725,by decide⟩] | 5 => ![⟨2726,by decide⟩,⟨543,by decide⟩,⟨2726,by decide⟩] | _ => ![⟨8,by decide⟩,⟨548,by decide⟩,⟨2727,by decide⟩]

def ntree11RRLRRRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨2728,by decide⟩,⟨549,by decide⟩] | 1 => ![⟨2391,by decide⟩,⟨548,by decide⟩,⟨548,by decide⟩] | 2 => ![⟨2392,by decide⟩,⟨2728,by decide⟩,⟨1768,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨2729,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨512,by decide⟩,⟨2730,by decide⟩,⟨512,by decide⟩] | 5 => ![⟨2369,by decide⟩,⟨2729,by decide⟩,⟨2687,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨2731,by decide⟩,⟨10,by decide⟩] | _ => ![⟨514,by decide⟩,⟨2732,by decide⟩,⟨514,by decide⟩]

def ntree11RRLRRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRLRRRRLL i else ntree11RRLRRRRLR (i - 7)

def ntree11RRLRRRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2374,by decide⟩,⟨2731,by decide⟩,⟨2690,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨2733,by decide⟩,⟨529,by decide⟩] | 2 => ![⟨2382,by decide⟩,⟨2731,by decide⟩,⟨2696,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨2734,by decide⟩,⟨8,by decide⟩] | 4 => ![⟨876,by decide⟩,⟨2731,by decide⟩,⟨1331,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨544,by decide⟩,⟨2735,by decide⟩] | 6 => ![⟨1380,by decide⟩,⟨2736,by decide⟩,⟨500,by decide⟩] | _ => ![⟨2411,by decide⟩,⟨2737,by decide⟩,⟨504,by decide⟩]

def ntree11RRLRRRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨582,by decide⟩,⟨582,by decide⟩] | 1 => ![⟨1391,by decide⟩,⟨2738,by decide⟩,⟨510,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨588,by decide⟩,⟨588,by decide⟩] | 3 => ![⟨2739,by decide⟩,⟨10,by decide⟩,⟨2739,by decide⟩] | 4 => ![⟨2415,by decide⟩,⟨2415,by decide⟩,⟨2690,by decide⟩] | 5 => ![⟨2419,by decide⟩,⟨2740,by decide⟩,⟨2694,by decide⟩] | 6 => ![⟨1389,by decide⟩,⟨1389,by decide⟩,⟨2696,by decide⟩] | _ => ![⟨1402,by decide⟩,⟨2741,by decide⟩,⟨2699,by decide⟩]

def ntree11RRLRRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRLRRRRRL i else ntree11RRLRRRRRR (i - 8)

def ntree11RRLRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRLRRRRL i else ntree11RRLRRRRR (i - 15)

def ntree11RRLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RRLRRRL i else ntree11RRLRRRR (i - 31)

def ntree11RRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11RRLRRL i else ntree11RRLRRR (i - 62)

def ntree11RRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 124 then ntree11RRLRL i else ntree11RRLRR (i - 124)

def ntree11RRL (i : Nat) : Fin 3 → Fin 3109 := if i < 247 then ntree11RRLL i else ntree11RRLR (i - 247)

def ntree11RRRLLLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1406,by decide⟩,⟨2742,by decide⟩,⟨570,by decide⟩] | 1 => ![⟨1411,by decide⟩,⟨2743,by decide⟩,⟨573,by decide⟩] | 2 => ![⟨1406,by decide⟩,⟨2744,by decide⟩,⟨526,by decide⟩] | 3 => ![⟨1411,by decide⟩,⟨2745,by decide⟩,⟨529,by decide⟩] | 4 => ![⟨2415,by decide⟩,⟨2746,by decide⟩,⟨529,by decide⟩] | 5 => ![⟨2415,by decide⟩,⟨2747,by decide⟩,⟨506,by decide⟩] | _ => ![⟨617,by decide⟩,⟨615,by decide⟩,⟨615,by decide⟩]

def ntree11RRRLLLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1415,by decide⟩,⟨2748,by decide⟩,⟨582,by decide⟩] | 1 => ![⟨1415,by decide⟩,⟨2749,by decide⟩,⟨529,by decide⟩] | 2 => ![⟨617,by decide⟩,⟨617,by decide⟩,⟨617,by decide⟩] | 3 => ![⟨2750,by decide⟩,⟨2751,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨2752,by decide⟩,⟨2710,by decide⟩,⟨506,by decide⟩] | 5 => ![⟨2739,by decide⟩,⟨10,by decide⟩,⟨2753,by decide⟩] | 6 => ![⟨2739,by decide⟩,⟨2376,by decide⟩,⟨2739,by decide⟩] | _ => ![⟨2415,by decide⟩,⟨2415,by decide⟩,⟨2714,by decide⟩]

def ntree11RRRLLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRRLLLLLL i else ntree11RRRLLLLLR (i - 7)

def ntree11RRRLLLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2419,by decide⟩,⟨2746,by decide⟩,⟨2719,by decide⟩] | 1 => ![⟨2754,by decide⟩,⟨573,by decide⟩,⟨2755,by decide⟩] | 2 => ![⟨1411,by decide⟩,⟨1411,by decide⟩,⟨2722,by decide⟩] | 3 => ![⟨2754,by decide⟩,⟨10,by decide⟩,⟨2754,by decide⟩] | 4 => ![⟨2756,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨1420,by decide⟩,⟨2757,by decide⟩,⟨2724,by decide⟩] | _ => ![⟨2758,by decide⟩,⟨617,by decide⟩,⟨2758,by decide⟩]

def ntree11RRRLLLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1380,by decide⟩,⟨2759,by decide⟩,⟨526,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨2760,by decide⟩,⟨4,by decide⟩] | 2 => ![⟨2411,by decide⟩,⟨2761,by decide⟩,⟨548,by decide⟩] | 3 => ![⟨584,by decide⟩,⟨633,by decide⟩,⟨633,by decide⟩] | 4 => ![⟨1391,by decide⟩,⟨2762,by decide⟩,⟨529,by decide⟩] | 5 => ![⟨8,by decide⟩,⟨2763,by decide⟩,⟨8,by decide⟩] | 6 => ![⟨2764,by decide⟩,⟨10,by decide⟩,⟨2764,by decide⟩] | _ => ![⟨2764,by decide⟩,⟨2376,by decide⟩,⟨2764,by decide⟩]

def ntree11RRRLLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRRLLLLRL i else ntree11RRRLLLLRR (i - 7)

def ntree11RRRLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRRLLLLL i else ntree11RRRLLLLR (i - 15)

def ntree11RRRLLLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2764,by decide⟩,⟨10,by decide⟩,⟨2765,by decide⟩] | 1 => ![⟨2754,by decide⟩,⟨10,by decide⟩,⟨2766,by decide⟩] | 2 => ![⟨1389,by decide⟩,⟨2767,by decide⟩,⟨544,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨2768,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1824,by decide⟩,⟨2741,by decide⟩,⟨2769,by decide⟩] | 5 => ![⟨646,by decide⟩,⟨8,by decide⟩,⟨2346,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2770,by decide⟩]

def ntree11RRRLLLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2771,by decide⟩] | 1 => ![⟨644,by decide⟩,⟨10,by decide⟩,⟨2349,by decide⟩] | 2 => ![⟨2772,by decide⟩,⟨2772,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨2772,by decide⟩,⟨2772,by decide⟩,⟨2349,by decide⟩] | 4 => ![⟨2739,by decide⟩,⟨2689,by decide⟩,⟨2739,by decide⟩] | 5 => ![⟨2772,by decide⟩,⟨2772,by decide⟩,⟨2690,by decide⟩] | 6 => ![⟨2773,by decide⟩,⟨2773,by decide⟩,⟨2691,by decide⟩] | _ => ![⟨1460,by decide⟩,⟨523,by decide⟩,⟨2774,by decide⟩]

def ntree11RRRLLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRRLLLRLL i else ntree11RRRLLLRLR (i - 7)

def ntree11RRRLLLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1826,by decide⟩,⟨524,by decide⟩,⟨2775,by decide⟩] | 1 => ![⟨2776,by decide⟩,⟨2772,by decide⟩,⟨1460,by decide⟩] | 2 => ![⟨2776,by decide⟩,⟨2777,by decide⟩,⟨2452,by decide⟩] | 3 => ![⟨652,by decide⟩,⟨10,by decide⟩,⟨2349,by decide⟩] | 4 => ![⟨1389,by decide⟩,⟨2778,by decide⟩,⟨654,by decide⟩] | 5 => ![⟨2779,by decide⟩,⟨2779,by decide⟩,⟨8,by decide⟩] | 6 => ![⟨2780,by decide⟩,⟨2780,by decide⟩,⟨521,by decide⟩] | _ => ![⟨1831,by decide⟩,⟨2781,by decide⟩,⟨523,by decide⟩]

def ntree11RRRLLLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1832,by decide⟩,⟨2782,by decide⟩,⟨524,by decide⟩] | 1 => ![⟨2779,by decide⟩,⟨2783,by decide⟩,⟨41,by decide⟩] | 2 => ![⟨584,by decide⟩,⟨2784,by decide⟩,⟨584,by decide⟩] | 3 => ![⟨2460,by decide⟩,⟨573,by decide⟩,⟨2785,by decide⟩] | 4 => ![⟨2786,by decide⟩,⟨2743,by decide⟩,⟨2785,by decide⟩] | 5 => ![⟨1411,by decide⟩,⟨2757,by decide⟩,⟨544,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨544,by decide⟩,⟨2787,by decide⟩] | _ => ![⟨659,by decide⟩,⟨10,by decide⟩,⟨1344,by decide⟩]

def ntree11RRRLLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRRLLLRRL i else ntree11RRRLLLRRR (i - 8)

def ntree11RRRLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRRLLLRL i else ntree11RRRLLLRR (i - 15)

def ntree11RRRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 30 then ntree11RRRLLLL i else ntree11RRRLLLR (i - 30)

def ntree11RRRLLRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨659,by decide⟩,⟨1802,by decide⟩,⟨2349,by decide⟩] | 1 => ![⟨2788,by decide⟩,⟨617,by decide⟩,⟨617,by decide⟩] | 2 => ![⟨644,by decide⟩,⟨2376,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨2789,by decide⟩,⟨2789,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨2789,by decide⟩,⟨2790,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨2460,by decide⟩,⟨2689,by decide⟩,⟨2460,by decide⟩] | _ => ![⟨2789,by decide⟩,⟨2789,by decide⟩,⟨2349,by decide⟩]

def ntree11RRRLLRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2789,by decide⟩,⟨2789,by decide⟩,⟨2714,by decide⟩] | 1 => ![⟨2791,by decide⟩,⟨2790,by decide⟩,⟨2753,by decide⟩] | 2 => ![⟨2792,by decide⟩,⟨2715,by decide⟩,⟨2792,by decide⟩] | 3 => ![⟨2793,by decide⟩,⟨2793,by decide⟩,⟨2716,by decide⟩] | 4 => ![⟨1460,by decide⟩,⟨544,by decide⟩,⟨2794,by decide⟩] | 5 => ![⟨1460,by decide⟩,⟨546,by decide⟩,⟨2795,by decide⟩] | 6 => ![⟨2796,by decide⟩,⟨2789,by decide⟩,⟨1460,by decide⟩] | _ => ![⟨2796,by decide⟩,⟨2797,by decide⟩,⟨2452,by decide⟩]

def ntree11RRRLLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRRLLRLLL i else ntree11RRRLLRLLR (i - 7)

def ntree11RRRLLRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨659,by decide⟩,⟨2689,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨142,by decide⟩,⟨2798,by decide⟩,⟨142,by decide⟩] | 2 => ![⟨1831,by decide⟩,⟨2799,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨2789,by decide⟩,⟨2800,by decide⟩,⟨573,by decide⟩] | 4 => ![⟨2801,by decide⟩,⟨2801,by decide⟩,⟨543,by decide⟩] | 5 => ![⟨2793,by decide⟩,⟨2793,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨2802,by decide⟩,⟨2802,by decide⟩,⟨543,by decide⟩] | _ => ![⟨1831,by decide⟩,⟨2803,by decide⟩,⟨35,by decide⟩]

def ntree11RRRLLRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2789,by decide⟩,⟨2804,by decide⟩,⟨65,by decide⟩] | 1 => ![⟨2789,by decide⟩,⟨2797,by decide⟩,⟨35,by decide⟩] | 2 => ![⟨1853,by decide⟩,⟨2767,by decide⟩,⟨2787,by decide⟩] | 3 => ![⟨677,by decide⟩,⟨2763,by decide⟩,⟨2346,by decide⟩] | 4 => ![⟨675,by decide⟩,⟨2376,by decide⟩,⟨2771,by decide⟩] | 5 => ![⟨2805,by decide⟩,⟨584,by decide⟩,⟨584,by decide⟩] | 6 => ![⟨675,by decide⟩,⟨2376,by decide⟩,⟨2771,by decide⟩] | _ => ![⟨675,by decide⟩,⟨2768,by decide⟩,⟨2349,by decide⟩]

def ntree11RRRLLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRRLLRLRL i else ntree11RRRLLRLRR (i - 8)

def ntree11RRRLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRRLLRLL i else ntree11RRRLLRLR (i - 15)

def ntree11RRRLLRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2460,by decide⟩,⟨2731,by decide⟩,⟨2460,by decide⟩] | 1 => ![⟨2772,by decide⟩,⟨2806,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨2764,by decide⟩,⟨2731,by decide⟩,⟨2764,by decide⟩] | 3 => ![⟨2807,by decide⟩,⟨2732,by decide⟩,⟨2807,by decide⟩] | 4 => ![⟨2808,by decide⟩,⟨2806,by decide⟩,⟨2765,by decide⟩] | 5 => ![⟨659,by decide⟩,⟨2731,by decide⟩,⟨2809,by decide⟩] | _ => ![⟨1831,by decide⟩,⟨2810,by decide⟩,⟨10,by decide⟩]

def ntree11RRRLLRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1832,by decide⟩,⟨2811,by decide⟩,⟨514,by decide⟩] | 1 => ![⟨2779,by decide⟩,⟨2812,by decide⟩,⟨8,by decide⟩] | 2 => ![⟨2813,by decide⟩,⟨2813,by decide⟩,⟨4,by decide⟩] | 3 => ![⟨2814,by decide⟩,⟨2814,by decide⟩,⟨8,by decide⟩] | 4 => ![⟨2815,by decide⟩,⟨2814,by decide⟩,⟨2683,by decide⟩] | 5 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨2482,by decide⟩] | 6 => ![⟨1748,by decide⟩,⟨690,by decide⟩,⟨2816,by decide⟩] | _ => ![⟨2817,by decide⟩,⟨2817,by decide⟩,⟨8,by decide⟩]

def ntree11RRRLLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRRLLRRLL i else ntree11RRRLLRRLR (i - 7)

def ntree11RRRLLRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2817,by decide⟩,⟨2817,by decide⟩,⟨2484,by decide⟩] | 1 => ![⟨1858,by decide⟩,⟨2818,by decide⟩,⟨160,by decide⟩] | 2 => ![⟨1859,by decide⟩,⟨2819,by decide⟩,⟨166,by decide⟩] | 3 => ![⟨1872,by decide⟩,⟨2820,by decide⟩,⟨2488,by decide⟩] | 4 => ![⟨1756,by decide⟩,⟨701,by decide⟩,⟨2821,by decide⟩] | 5 => ![⟨1864,by decide⟩,⟨2820,by decide⟩,⟨173,by decide⟩] | 6 => ![⟨2817,by decide⟩,⟨2822,by decide⟩,⟨184,by decide⟩] | _ => ![⟨2823,by decide⟩,⟨2817,by decide⟩,⟨2364,by decide⟩]

def ntree11RRRLLRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2823,by decide⟩,⟨2822,by decide⟩,⟨2491,by decide⟩] | 1 => ![⟨1858,by decide⟩,⟨2824,by decide⟩,⟨704,by decide⟩] | 2 => ![⟨1859,by decide⟩,⟨2825,by decide⟩,⟨706,by decide⟩] | 3 => ![⟨2826,by decide⟩,⟨1859,by decide⟩,⟨2703,by decide⟩] | 4 => ![⟨2703,by decide⟩,⟨10,by decide⟩,⟨2703,by decide⟩] | 5 => ![⟨1864,by decide⟩,⟨2827,by decide⟩,⟨710,by decide⟩] | 6 => ![⟨1864,by decide⟩,⟨2827,by decide⟩,⟨2828,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2482,by decide⟩]

def ntree11RRRLLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRRLLRRRL i else ntree11RRRLLRRRR (i - 8)

def ntree11RRRLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRRLLRRL i else ntree11RRRLLRRR (i - 15)

def ntree11RRRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RRRLLRL i else ntree11RRRLLRR (i - 31)

def ntree11RRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 61 then ntree11RRRLLL i else ntree11RRRLLR (i - 61)

def ntree11RRRLRLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1858,by decide⟩,⟨2829,by decide⟩,⟨715,by decide⟩] | 1 => ![⟨1859,by decide⟩,⟨2830,by decide⟩,⟨716,by decide⟩] | 2 => ![⟨1872,by decide⟩,⟨2827,by decide⟩,⟨2831,by decide⟩] | 3 => ![⟨1872,by decide⟩,⟨2832,by decide⟩,⟨2833,by decide⟩] | 4 => ![⟨1864,by decide⟩,⟨2832,by decide⟩,⟨720,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨2834,by decide⟩,⟨173,by decide⟩] | _ => ![⟨1322,by decide⟩,⟨2834,by decide⟩,⟨2488,by decide⟩]

def ntree11RRRLRLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1858,by decide⟩,⟨2835,by decide⟩,⟨220,by decide⟩] | 1 => ![⟨1866,by decide⟩,⟨2836,by decide⟩,⟨726,by decide⟩] | 2 => ![⟨1859,by decide⟩,⟨2837,by decide⟩,⟨227,by decide⟩] | 3 => ![⟨1867,by decide⟩,⟨2838,by decide⟩,⟨727,by decide⟩] | 4 => ![⟨1864,by decide⟩,⟨2839,by decide⟩,⟨229,by decide⟩] | 5 => ![⟨1874,by decide⟩,⟨2840,by decide⟩,⟨728,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨2731,by decide⟩,⟨2482,by decide⟩] | _ => ![⟨514,by decide⟩,⟨2732,by decide⟩,⟨2841,by decide⟩]

def ntree11RRRLRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRRLRLLLL i else ntree11RRRLRLLLR (i - 7)

def ntree11RRRLRLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2817,by decide⟩,⟨2842,by decide⟩,⟨234,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨2734,by decide⟩,⟨2484,by decide⟩] | 2 => ![⟨2843,by decide⟩,⟨1859,by decide⟩,⟨2739,by decide⟩] | 3 => ![⟨1322,by decide⟩,⟨690,by decide⟩,⟨2844,by decide⟩] | 4 => ![⟨1913,by decide⟩,⟨1913,by decide⟩,⟨617,by decide⟩] | 5 => ![⟨2843,by decide⟩,⟨2825,by decide⟩,⟨2845,by decide⟩] | 6 => ![⟨2846,by decide⟩,⟨1864,by decide⟩,⟨2754,by decide⟩] | _ => ![⟨2847,by decide⟩,⟨1913,by decide⟩,⟨2758,by decide⟩]

def ntree11RRRLRLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1858,by decide⟩,⟨2848,by decide⟩,⟨289,by decide⟩] | 1 => ![⟨2813,by decide⟩,⟨2849,by decide⟩,⟨290,by decide⟩] | 2 => ![⟨2814,by decide⟩,⟨2850,by decide⟩,⟨291,by decide⟩] | 3 => ![⟨1864,by decide⟩,⟨2851,by decide⟩,⟨293,by decide⟩] | 4 => ![⟨2817,by decide⟩,⟨2852,by decide⟩,⟨291,by decide⟩] | 5 => ![⟨2853,by decide⟩,⟨1859,by decide⟩,⟨2764,by decide⟩] | 6 => ![⟨2853,by decide⟩,⟨2825,by decide⟩,⟨2854,by decide⟩] | _ => ![⟨10,by decide⟩,⟨2376,by decide⟩,⟨2855,by decide⟩]

def ntree11RRRLRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRRLRLLRL i else ntree11RRRLRLLRR (i - 8)

def ntree11RRRLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRRLRLLL i else ntree11RRRLRLLR (i - 15)

def ntree11RRRLRLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2856,by decide⟩,⟨1559,by decide⟩,⟨2754,by decide⟩] | 1 => ![⟨2857,by decide⟩,⟨2858,by decide⟩,⟨173,by decide⟩] | 2 => ![⟨2526,by decide⟩,⟨2859,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨2860,by decide⟩,⟨2860,by decide⟩,⟨514,by decide⟩] | 4 => ![⟨1896,by decide⟩,⟨2861,by decide⟩,⟨778,by decide⟩] | 5 => ![⟨2525,by decide⟩,⟨2862,by decide⟩,⟨8,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2863,by decide⟩]

def ntree11RRRLRLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2864,by decide⟩] | 1 => ![⟨2865,by decide⟩,⟨1864,by decide⟩,⟨2460,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2866,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2867,by decide⟩] | 4 => ![⟨2865,by decide⟩,⟨2820,by decide⟩,⟨2566,by decide⟩] | 5 => ![⟨2868,by decide⟩,⟨2868,by decide⟩,⟨142,by decide⟩] | 6 => ![⟨2868,by decide⟩,⟨2869,by decide⟩,⟨344,by decide⟩] | _ => ![⟨2870,by decide⟩,⟨2871,by decide⟩,⟨10,by decide⟩]

def ntree11RRRLRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRRLRLRLL i else ntree11RRRLRLRLR (i - 7)

def ntree11RRRLRLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2872,by decide⟩,⟨2873,by decide⟩,⟨270,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨796,by decide⟩,⟨796,by decide⟩] | 2 => ![⟨617,by decide⟩,⟨2874,by decide⟩,⟨801,by decide⟩] | 3 => ![⟨1577,by decide⟩,⟨1949,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨2526,by decide⟩,⟨2875,by decide⟩,⟨799,by decide⟩] | 5 => ![⟨2865,by decide⟩,⟨2839,by decide⟩,⟨2876,by decide⟩] | 6 => ![⟨2857,by decide⟩,⟨2877,by decide⟩,⟨270,by decide⟩] | _ => ![⟨2526,by decide⟩,⟨2878,by decide⟩,⟨816,by decide⟩]

def ntree11RRRLRLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2860,by decide⟩,⟨2879,by decide⟩,⟨817,by decide⟩] | 1 => ![⟨1559,by decide⟩,⟨2880,by decide⟩,⟨822,by decide⟩] | 2 => ![⟨2525,by decide⟩,⟨2881,by decide⟩,⟨824,by decide⟩] | 3 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨2349,by decide⟩] | 4 => ![⟨2882,by decide⟩,⟨2882,by decide⟩,⟨357,by decide⟩] | 5 => ![⟨2882,by decide⟩,⟨2882,by decide⟩,⟨2579,by decide⟩] | 6 => ![⟨2883,by decide⟩,⟨2883,by decide⟩,⟨10,by decide⟩] | _ => ![⟨2883,by decide⟩,⟨2883,by decide⟩,⟨2349,by decide⟩]

def ntree11RRRLRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRRLRLRRL i else ntree11RRRLRLRRR (i - 8)

def ntree11RRRLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRRLRLRL i else ntree11RRRLRLRR (i - 15)

def ntree11RRRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RRRLRLL i else ntree11RRRLRLR (i - 31)

def ntree11RRRLRRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2884,by decide⟩,⟨2883,by decide⟩,⟨1748,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨510,by decide⟩,⟨2885,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨173,by decide⟩,⟨2886,by decide⟩] | 3 => ![⟨1872,by decide⟩,⟨2887,by decide⟩,⟨2353,by decide⟩] | 4 => ![⟨1322,by decide⟩,⟨848,by decide⟩,⟨2888,by decide⟩] | 5 => ![⟨1864,by decide⟩,⟨2820,by decide⟩,⟨2591,by decide⟩] | _ => ![⟨10,by decide⟩,⟨2689,by decide⟩,⟨10,by decide⟩]

def ntree11RRRLRRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2889,by decide⟩,⟨1864,by decide⟩,⟨2890,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2349,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨2376,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1864,by decide⟩,⟨2891,by decide⟩,⟨529,by decide⟩] | 4 => ![⟨1864,by decide⟩,⟨2891,by decide⟩,⟨2705,by decide⟩] | 5 => ![⟨2892,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | 6 => ![⟨2889,by decide⟩,⟨2891,by decide⟩,⟨2893,by decide⟩] | _ => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨2714,by decide⟩]

def ntree11RRRLRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRRLRRLLL i else ntree11RRRLRRLLR (i - 7)

def ntree11RRRLRRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2889,by decide⟩,⟨2820,by decide⟩,⟨2894,by decide⟩] | 1 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨2716,by decide⟩] | 2 => ![⟨1872,by decide⟩,⟨2891,by decide⟩,⟨2719,by decide⟩] | 3 => ![⟨1872,by decide⟩,⟨2895,by decide⟩,⟨2720,by decide⟩] | 4 => ![⟨2896,by decide⟩,⟨2897,by decide⟩,⟨2898,by decide⟩] | 5 => ![⟨869,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩] | 6 => ![⟨2899,by decide⟩,⟨2883,by decide⟩,⟨2900,by decide⟩] | _ => ![⟨2901,by decide⟩,⟨2376,by decide⟩,⟨2902,by decide⟩]

def ntree11RRRLRRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2883,by decide⟩,⟨2903,by decide⟩,⟨529,by decide⟩] | 1 => ![⟨2883,by decide⟩,⟨2903,by decide⟩,⟨2705,by decide⟩] | 2 => ![⟨1874,by decide⟩,⟨2904,by decide⟩,⟨558,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨2597,by decide⟩,⟨2690,by decide⟩] | 4 => ![⟨514,by decide⟩,⟨2905,by decide⟩,⟨2691,by decide⟩] | 5 => ![⟨1864,by decide⟩,⟨2906,by decide⟩,⟨72,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨2907,by decide⟩,⟨2349,by decide⟩] | _ => ![⟨1864,by decide⟩,⟨2908,by decide⟩,⟨872,by decide⟩]

def ntree11RRRLRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRRLRRLRL i else ntree11RRRLRRLRR (i - 8)

def ntree11RRRLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRRLRRLL i else ntree11RRRLRRLR (i - 15)

def ntree11RRRLRRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2374,by decide⟩,⟨2909,by decide⟩,⟨2910,by decide⟩] | 1 => ![⟨2901,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨1864,by decide⟩,⟨2911,by decide⟩,⟨573,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨2912,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨1389,by decide⟩,⟨2913,by decide⟩,⟨690,by decide⟩] | 5 => ![⟨2882,by decide⟩,⟨2914,by decide⟩,⟨879,by decide⟩] | _ => ![⟨357,by decide⟩,⟨2915,by decide⟩,⟨357,by decide⟩]

def ntree11RRRLRRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2883,by decide⟩,⟨2916,by decide⟩,⟨573,by decide⟩] | 1 => ![⟨2917,by decide⟩,⟨2917,by decide⟩,⟨883,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨2918,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1389,by decide⟩,⟨2919,by decide⟩,⟨510,by decide⟩] | 4 => ![⟨1864,by decide⟩,⟨2920,by decide⟩,⟨438,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨2921,by decide⟩,⟨10,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨2922,by decide⟩,⟨10,by decide⟩] | _ => ![⟨2526,by decide⟩,⟨2923,by decide⟩,⟨510,by decide⟩]

def ntree11RRRLRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRRLRRRLL i else ntree11RRRLRRRLR (i - 7)

def ntree11RRRLRRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨245,by decide⟩,⟨2924,by decide⟩,⟨2690,by decide⟩] | 1 => ![⟨2925,by decide⟩,⟨883,by decide⟩,⟨2925,by decide⟩] | 2 => ![⟨1872,by decide⟩,⟨2920,by decide⟩,⟨2631,by decide⟩] | 3 => ![⟨1322,by decide⟩,⟨2921,by decide⟩,⟨1322,by decide⟩] | 4 => ![⟨1322,by decide⟩,⟨2922,by decide⟩,⟨1322,by decide⟩] | 5 => ![⟨2527,by decide⟩,⟨2923,by decide⟩,⟨2694,by decide⟩] | 6 => ![⟨2632,by decide⟩,⟨1389,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1987,by decide⟩,⟨2926,by decide⟩,⟨896,by decide⟩]

def ntree11RRRLRRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨895,by decide⟩,⟨2927,by decide⟩,⟨895,by decide⟩] | 1 => ![⟨1987,by decide⟩,⟨2928,by decide⟩,⟨901,by decide⟩] | 2 => ![⟨895,by decide⟩,⟨2929,by decide⟩,⟨895,by decide⟩] | 3 => ![⟨2526,by decide⟩,⟨2930,by decide⟩,⟨529,by decide⟩] | 4 => ![⟨245,by decide⟩,⟨10,by decide⟩,⟨2714,by decide⟩] | 5 => ![⟨883,by decide⟩,⟨883,by decide⟩,⟨2931,by decide⟩] | 6 => ![⟨2925,by decide⟩,⟨902,by decide⟩,⟨2932,by decide⟩] | _ => ![⟨2527,by decide⟩,⟨2930,by decide⟩,⟨2719,by decide⟩]

def ntree11RRRLRRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRRLRRRRL i else ntree11RRRLRRRRR (i - 8)

def ntree11RRRLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRRLRRRL i else ntree11RRRLRRRR (i - 15)

def ntree11RRRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RRRLRRL i else ntree11RRRLRRR (i - 31)

def ntree11RRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11RRRLRL i else ntree11RRRLRR (i - 62)

def ntree11RRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 123 then ntree11RRRLL i else ntree11RRRLR (i - 123)

def ntree11RRRRLLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2933,by decide⟩,⟨2912,by decide⟩,⟨1579,by decide⟩] | 1 => ![⟨1970,by decide⟩,⟨2934,by decide⟩,⟨912,by decide⟩] | 2 => ![⟨1970,by decide⟩,⟨2935,by decide⟩,⟨918,by decide⟩] | 3 => ![⟨2882,by decide⟩,⟨2936,by decide⟩,⟨458,by decide⟩] | 4 => ![⟨2917,by decide⟩,⟨2937,by decide⟩,⟨902,by decide⟩] | 5 => ![⟨2938,by decide⟩,⟨529,by decide⟩,⟨2939,by decide⟩] | _ => ![⟨2938,by decide⟩,⟨270,by decide⟩,⟨2940,by decide⟩]

def ntree11RRRRLLLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨2653,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨304,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | 3 => ![⟨2526,by decide⟩,⟨2526,by decide⟩,⟨2690,by decide⟩] | 4 => ![⟨1970,by decide⟩,⟨1970,by decide⟩,⟨2941,by decide⟩] | 5 => ![⟨2942,by decide⟩,⟨10,by decide⟩,⟨2943,by decide⟩] | 6 => ![⟨1864,by decide⟩,⟨1864,by decide⟩,⟨2659,by decide⟩] | _ => ![⟨652,by decide⟩,⟨173,by decide⟩,⟨173,by decide⟩]

def ntree11RRRRLLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRRRLLLLL i else ntree11RRRRLLLLR (i - 7)

def ntree11RRRRLLLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨2526,by decide⟩,⟨2526,by decide⟩,⟨2690,by decide⟩] | 2 => ![⟨1874,by decide⟩,⟨2944,by decide⟩,⟨653,by decide⟩] | 3 => ![⟨1970,by decide⟩,⟨2945,by decide⟩,⟨931,by decide⟩] | 4 => ![⟨1831,by decide⟩,⟨2946,by decide⟩,⟨173,by decide⟩] | 5 => ![⟨1832,by decide⟩,⟨2947,by decide⟩,⟨701,by decide⟩] | 6 => ![⟨2374,by decide⟩,⟨2912,by decide⟩,⟨2948,by decide⟩] | _ => ![⟨895,by decide⟩,⟨895,by decide⟩,⟨2949,by decide⟩]

def ntree11RRRRLLLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2950,by decide⟩] | 1 => ![⟨2951,by decide⟩,⟨1864,by decide⟩,⟨2665,by decide⟩] | 2 => ![⟨2951,by decide⟩,⟨1914,by decide⟩,⟨2666,by decide⟩] | 3 => ![⟨2665,by decide⟩,⟨10,by decide⟩,⟨2952,by decide⟩] | 4 => ![⟨2953,by decide⟩,⟨270,by decide⟩,⟨2954,by decide⟩] | 5 => ![⟨2951,by decide⟩,⟨2820,by decide⟩,⟨2672,by decide⟩] | 6 => ![⟨2671,by decide⟩,⟨2859,by decide⟩,⟨2952,by decide⟩] | _ => ![⟨2014,by decide⟩,⟨2955,by decide⟩,⟨935,by decide⟩]

def ntree11RRRRLLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRRRLLLRL i else ntree11RRRRLLLRR (i - 8)

def ntree11RRRRLLL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRRRLLLL i else ntree11RRRRLLLR (i - 15)

def ntree11RRRRLLRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2956,by decide⟩,⟨514,by decide⟩,⟨2956,by decide⟩] | 1 => ![⟨2665,by decide⟩,⟨816,by decide⟩,⟨2957,by decide⟩] | 2 => ![⟨2956,by decide⟩,⟨817,by decide⟩,⟨2958,by decide⟩] | 3 => ![⟨2951,by decide⟩,⟨2839,by decide⟩,⟨2680,by decide⟩] | 4 => ![⟨2665,by decide⟩,⟨2731,by decide⟩,⟨2665,by decide⟩] | 5 => ![⟨2665,by decide⟩,⟨2731,by decide⟩,⟨2665,by decide⟩] | _ => ![⟨2671,by decide⟩,⟨2878,by decide⟩,⟨2957,by decide⟩]

def ntree11RRRRLLRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2959,by decide⟩,⟨2959,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨2960,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨2960,by decide⟩,⟨510,by decide⟩,⟨510,by decide⟩] | 3 => ![⟨2961,by decide⟩,⟨2959,by decide⟩,⟨1748,by decide⟩] | 4 => ![⟨2962,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩] | 5 => ![⟨2960,by decide⟩,⟨10,by decide⟩,⟨1318,by decide⟩] | 6 => ![⟨2683,by decide⟩,⟨9,by decide⟩,⟨2963,by decide⟩] | _ => ![⟨10,by decide⟩,⟨2964,by decide⟩,⟨10,by decide⟩]

def ntree11RRRRLLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRRRLLRLL i else ntree11RRRRLLRLR (i - 7)

def ntree11RRRRLLRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2965,by decide⟩,⟨2966,by decide⟩,⟨18,by decide⟩] | 1 => ![⟨1317,by decide⟩,⟨2964,by decide⟩,⟨1317,by decide⟩] | 2 => ![⟨2965,by decide⟩,⟨2965,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨2967,by decide⟩,⟨2965,by decide⟩,⟨1322,by decide⟩] | 4 => ![⟨1756,by decide⟩,⟨953,by decide⟩,⟨2968,by decide⟩] | 5 => ![⟨2701,by decide⟩,⟨960,by decide⟩,⟨2969,by decide⟩] | 6 => ![⟨2970,by decide⟩,⟨2971,by decide⟩,⟨11,by decide⟩] | _ => ![⟨2972,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩]

def ntree11RRRRLLRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2972,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨10,by decide⟩,⟨2973,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨2970,by decide⟩,⟨2970,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨2960,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | 4 => ![⟨2974,by decide⟩,⟨2970,by decide⟩,⟨10,by decide⟩] | 5 => ![⟨2975,by decide⟩,⟨969,by decide⟩,⟨2976,by decide⟩] | 6 => ![⟨968,by decide⟩,⟨968,by decide⟩,⟨2977,by decide⟩] | _ => ![⟨2978,by decide⟩,⟨969,by decide⟩,⟨2979,by decide⟩]

def ntree11RRRRLLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRRRLLRRL i else ntree11RRRRLLRRR (i - 8)

def ntree11RRRRLLR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRRRLLRL i else ntree11RRRRLLRR (i - 15)

def ntree11RRRRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RRRRLLL i else ntree11RRRRLLR (i - 31)

def ntree11RRRRLRLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2978,by decide⟩,⟨975,by decide⟩,⟨2980,by decide⟩] | 1 => ![⟨2972,by decide⟩,⟨2964,by decide⟩,⟨2714,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨2981,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨1338,by decide⟩,⟨978,by decide⟩,⟨2982,by decide⟩] | 4 => ![⟨1350,by decide⟩,⟨984,by decide⟩,⟨2983,by decide⟩] | 5 => ![⟨2984,by decide⟩,⟨11,by decide⟩,⟨11,by decide⟩] | _ => ![⟨2984,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩]

def ntree11RRRRLRLLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2985,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨1322,by decide⟩,⟨2986,by decide⟩,⟨1322,by decide⟩] | 2 => ![⟨2726,by decide⟩,⟨986,by decide⟩,⟨2987,by decide⟩] | 3 => ![⟨2959,by decide⟩,⟨2988,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨2396,by decide⟩,⟨529,by decide⟩,⟨2989,by decide⟩] | 5 => ![⟨2390,by decide⟩,⟨548,by decide⟩,⟨2990,by decide⟩] | 6 => ![⟨10,by decide⟩,⟨2991,by decide⟩,⟨10,by decide⟩] | _ => ![⟨514,by decide⟩,⟨2992,by decide⟩,⟨514,by decide⟩]

def ntree11RRRRLRLL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRRRLRLLL i else ntree11RRRRLRLLR (i - 7)

def ntree11RRRRLRLRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2972,by decide⟩,⟨2991,by decide⟩,⟨2690,by decide⟩] | 1 => ![⟨1338,by decide⟩,⟨2991,by decide⟩,⟨1338,by decide⟩] | 2 => ![⟨2965,by decide⟩,⟨2993,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨2049,by decide⟩,⟨10,by decide⟩,⟨2994,by decide⟩] | 4 => ![⟨2049,by decide⟩,⟨10,by decide⟩,⟨2995,by decide⟩] | 5 => ![⟨2050,by decide⟩,⟨514,by decide⟩,⟨2996,by decide⟩] | 6 => ![⟨2049,by decide⟩,⟨529,by decide⟩,⟨2997,by decide⟩] | _ => ![⟨2050,by decide⟩,⟨558,by decide⟩,⟨2998,by decide⟩]

def ntree11RRRRLRLRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2057,by decide⟩,⟨999,by decide⟩,⟨2999,by decide⟩] | 1 => ![⟨2984,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨10,by decide⟩,⟨2986,by decide⟩,⟨10,by decide⟩] | 3 => ![⟨521,by decide⟩,⟨521,by decide⟩,⟨3000,by decide⟩] | 4 => ![⟨3001,by decide⟩,⟨3001,by decide⟩,⟨85,by decide⟩] | 5 => ![⟨85,by decide⟩,⟨85,by decide⟩,⟨3002,by decide⟩] | 6 => ![⟨2739,by decide⟩,⟨18,by decide⟩,⟨3003,by decide⟩] | _ => ![⟨2418,by decide⟩,⟨1004,by decide⟩,⟨3004,by decide⟩]

def ntree11RRRRLRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRRRLRLRL i else ntree11RRRRLRLRR (i - 8)

def ntree11RRRRLRL (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRRRLRLL i else ntree11RRRRLRLR (i - 15)

def ntree11RRRRLRRLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨3005,by decide⟩,⟨3006,by decide⟩,⟨86,by decide⟩] | 1 => ![⟨85,by decide⟩,⟨3007,by decide⟩,⟨85,by decide⟩] | 2 => ![⟨3005,by decide⟩,⟨3005,by decide⟩,⟨85,by decide⟩] | 3 => ![⟨3008,by decide⟩,⟨3009,by decide⟩,⟨969,by decide⟩] | 4 => ![⟨968,by decide⟩,⟨3010,by decide⟩,⟨968,by decide⟩] | 5 => ![⟨85,by decide⟩,⟨85,by decide⟩,⟨3011,by decide⟩] | _ => ![⟨10,by decide⟩,⟨1418,by decide⟩,⟨2714,by decide⟩]

def ntree11RRRRLRRLR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨2418,by decide⟩,⟨1026,by decide⟩,⟨3012,by decide⟩] | 1 => ![⟨1322,by decide⟩,⟨3013,by decide⟩,⟨2719,by decide⟩] | 2 => ![⟨3014,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | 3 => ![⟨1391,by decide⟩,⟨3015,by decide⟩,⟨10,by decide⟩] | 4 => ![⟨3001,by decide⟩,⟨3016,by decide⟩,⟨85,by decide⟩] | 5 => ![⟨10,by decide⟩,⟨3013,by decide⟩,⟨529,by decide⟩] | 6 => ![⟨1052,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨1053,by decide⟩,⟨1418,by decide⟩,⟨2690,by decide⟩]

def ntree11RRRRLRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 7 then ntree11RRRRLRRLL i else ntree11RRRRLRRLR (i - 7)

def ntree11RRRRLRRRL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨3017,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨3018,by decide⟩,⟨85,by decide⟩,⟨3018,by decide⟩] | 2 => ![⟨3018,by decide⟩,⟨85,by decide⟩,⟨3019,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨529,by decide⟩,⟨3020,by decide⟩] | 4 => ![⟨1052,by decide⟩,⟨529,by decide⟩,⟨529,by decide⟩] | 5 => ![⟨3021,by decide⟩,⟨1802,by decide⟩,⟨2400,by decide⟩] | 6 => ![⟨3022,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨3023,by decide⟩,⟨8,by decide⟩,⟨8,by decide⟩]

def ntree11RRRRLRRRR (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨3024,by decide⟩,⟨2768,by decide⟩,⟨1378,by decide⟩] | 1 => ![⟨3025,by decide⟩,⟨2763,by decide⟩,⟨2409,by decide⟩] | 2 => ![⟨3026,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩] | 3 => ![⟨3027,by decide⟩,⟨83,by decide⟩,⟨83,by decide⟩] | 4 => ![⟨3026,by decide⟩,⟨85,by decide⟩,⟨2448,by decide⟩] | 5 => ![⟨3028,by decide⟩,⟨1069,by decide⟩,⟨3028,by decide⟩] | 6 => ![⟨3029,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | _ => ![⟨3030,by decide⟩,⟨85,by decide⟩,⟨85,by decide⟩]

def ntree11RRRRLRRR (i : Nat) : Fin 3 → Fin 3109 := if i < 8 then ntree11RRRRLRRRL i else ntree11RRRRLRRRR (i - 8)

def ntree11RRRRLRR (i : Nat) : Fin 3 → Fin 3109 := if i < 15 then ntree11RRRRLRRL i else ntree11RRRRLRRR (i - 15)

def ntree11RRRRLR (i : Nat) : Fin 3 → Fin 3109 := if i < 31 then ntree11RRRRLRL i else ntree11RRRRLRR (i - 31)

def ntree11RRRRL (i : Nat) : Fin 3 → Fin 3109 := if i < 62 then ntree11RRRRLL i else ntree11RRRRLR (i - 62)

def ntree11RRRRRLLLL (i : Nat) : Fin 3 → Fin 3109 := match i with | 0 => ![⟨3031,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨2960,by decide⟩,⟨1802,by decide⟩,⟨2467,by decide⟩] | 2 => ![⟨3032,by decide⟩,⟨11,by decide⟩,⟨1339,by decide⟩] | 3 => ![⟨3033,by decide⟩,⟨2091,by decide⟩,⟨2348,by decide⟩] | 4 => ![⟨3034,by decide⟩,⟨2093,by decide⟩,⟨2377,by decide⟩] | 5 => ![⟨2792,by decide⟩,⟨10,by decide⟩,⟨2792,by decide⟩] | _ => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2714,by decide⟩]

end Paper2.Certificates.Q6.Coverage
