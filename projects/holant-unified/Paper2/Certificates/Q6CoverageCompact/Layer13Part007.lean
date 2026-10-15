import Paper2.Certificates.Q6CoverageCompact.Layer13Part006

namespace Paper2.Certificates.Q6.Coverage

def ntree13RRRLLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13RRRLLRLL i else ntree13RRRLLRLR (i - 9)

def ntree13RRRLLRRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨8,by decide⟩,⟨1852,by decide⟩,⟨1856,by decide⟩] | 1 => ![⟨1632,by decide⟩,⟨1853,by decide⟩,⟨1857,by decide⟩] | 2 => ![⟨375,by decide⟩,⟨375,by decide⟩,⟨1293,by decide⟩] | _ => ![⟨1830,by decide⟩,⟨392,by decide⟩,⟨1294,by decide⟩]

def ntree13RRRLLRRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨8,by decide⟩,⟨1854,by decide⟩,⟨1856,by decide⟩] | 1 => ![⟨1806,by decide⟩,⟨451,by decide⟩,⟨451,by decide⟩] | 2 => ![⟨1668,by decide⟩,⟨1858,by decide⟩,⟨1668,by decide⟩] | 3 => ![⟨1607,by decide⟩,⟨1859,by decide⟩,⟨1859,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1860,by decide⟩,⟨1860,by decide⟩]

def ntree13RRRLLRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13RRRLLRRLL i else ntree13RRRLLRRLR (i - 4)

def ntree13RRRLLRRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1806,by decide⟩,⟨1860,by decide⟩,⟨1860,by decide⟩] | 1 => ![⟨1607,by decide⟩,⟨1861,by decide⟩,⟨1861,by decide⟩] | 2 => ![⟨1862,by decide⟩,⟨414,by decide⟩,⟨1038,by decide⟩] | 3 => ![⟨1819,by decide⟩,⟨20,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1038,by decide⟩,⟨1860,by decide⟩,⟨1863,by decide⟩]

def ntree13RRRLLRRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1275,by decide⟩,⟨1864,by decide⟩,⟨1860,by decide⟩] | 1 => ![⟨1865,by decide⟩,⟨1275,by decide⟩,⟨111,by decide⟩] | 2 => ![⟨1246,by decide⟩,⟨1866,by decide⟩,⟨1860,by decide⟩] | 3 => ![⟨1004,by decide⟩,⟨1860,by decide⟩,⟨1867,by decide⟩] | _ => ![⟨1633,by decide⟩,⟨1633,by decide⟩,⟨1868,by decide⟩]

def ntree13RRRLLRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13RRRLLRRRL i else ntree13RRRLLRRRR (i - 5)

def ntree13RRRLLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13RRRLLRRL i else ntree13RRRLLRRR (i - 9)

def ntree13RRRLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 19 then ntree13RRRLLRL i else ntree13RRRLLRR (i - 19)

def ntree13RRRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 37 then ntree13RRRLLL i else ntree13RRRLLR (i - 37)

def ntree13RRRLRLLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨20,by decide⟩,⟨1293,by decide⟩] | 1 => ![⟨1607,by decide⟩,⟨1869,by decide⟩,⟨1869,by decide⟩] | 2 => ![⟨1668,by decide⟩,⟨1870,by decide⟩,⟨1870,by decide⟩] | _ => ![⟨1607,by decide⟩,⟨1871,by decide⟩,⟨1871,by decide⟩]

def ntree13RRRLRLLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1872,by decide⟩,⟨1311,by decide⟩,⟨8,by decide⟩] | 1 => ![⟨1873,by decide⟩,⟨1312,by decide⟩,⟨9,by decide⟩] | 2 => ![⟨1874,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨1875,by decide⟩,⟨1313,by decide⟩,⟨8,by decide⟩] | _ => ![⟨1876,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13RRRLRLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13RRRLRLLLL i else ntree13RRRLRLLLR (i - 4)

def ntree13RRRLRLLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1876,by decide⟩,⟨1877,by decide⟩,⟨1232,by decide⟩] | 1 => ![⟨1688,by decide⟩,⟨1688,by decide⟩,⟨1878,by decide⟩] | 2 => ![⟨1879,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1880,by decide⟩,⟨1311,by decide⟩,⟨126,by decide⟩]

def ntree13RRRLRLLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1881,by decide⟩,⟨1312,by decide⟩,⟨127,by decide⟩] | 1 => ![⟨1882,by decide⟩,⟨1313,by decide⟩,⟨134,by decide⟩] | 2 => ![⟨1692,by decide⟩,⟨1883,by decide⟩,⟨1884,by decide⟩] | 3 => ![⟨1885,by decide⟩,⟨1320,by decide⟩,⟨144,by decide⟩] | _ => ![⟨1886,by decide⟩,⟨145,by decide⟩,⟨145,by decide⟩]

def ntree13RRRLRLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13RRRLRLLRL i else ntree13RRRLRLLRR (i - 4)

def ntree13RRRLRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13RRRLRLLL i else ntree13RRRLRLLR (i - 9)

def ntree13RRRLRLRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1887,by decide⟩,⟨1888,by decide⟩,⟨1601,by decide⟩] | 1 => ![⟨1889,by decide⟩,⟨1890,by decide⟩,⟨924,by decide⟩] | 2 => ![⟨1311,by decide⟩,⟨1311,by decide⟩,⟨536,by decide⟩] | _ => ![⟨1880,by decide⟩,⟨1311,by decide⟩,⟨544,by decide⟩]

def ntree13RRRLRLRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1807,by decide⟩,⟨1,by decide⟩,⟨537,by decide⟩] | 1 => ![⟨1806,by decide⟩,⟨0,by decide⟩,⟨536,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1891,by decide⟩,⟨1891,by decide⟩] | 3 => ![⟨924,by decide⟩,⟨1891,by decide⟩,⟨1892,by decide⟩] | _ => ![⟨1806,by decide⟩,⟨0,by decide⟩,⟨542,by decide⟩]

def ntree13RRRLRLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13RRRLRLRLL i else ntree13RRRLRLRLR (i - 4)

def ntree13RRRLRLRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨126,by decide⟩,⟨1891,by decide⟩,⟨1893,by decide⟩] | 1 => ![⟨1894,by decide⟩,⟨1311,by decide⟩,⟨169,by decide⟩] | 2 => ![⟨1894,by decide⟩,⟨1316,by decide⟩,⟨551,by decide⟩] | 3 => ![⟨1688,by decide⟩,⟨1883,by decide⟩,⟨1883,by decide⟩] | _ => ![⟨1895,by decide⟩,⟨1246,by decide⟩,⟨178,by decide⟩]

def ntree13RRRLRLRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1313,by decide⟩,⟨1896,by decide⟩,⟨1831,by decide⟩] | 1 => ![⟨924,by decide⟩,⟨1897,by decide⟩,⟨1898,by decide⟩] | 2 => ![⟨1115,by decide⟩,⟨1831,by decide⟩,⟨1899,by decide⟩] | 3 => ![⟨1900,by decide⟩,⟨1311,by decide⟩,⟨215,by decide⟩] | _ => ![⟨1901,by decide⟩,⟨1312,by decide⟩,⟨216,by decide⟩]

def ntree13RRRLRLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13RRRLRLRRL i else ntree13RRRLRLRRR (i - 5)

def ntree13RRRLRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13RRRLRLRL i else ntree13RRRLRLRR (i - 9)

def ntree13RRRLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 18 then ntree13RRRLRLL i else ntree13RRRLRLR (i - 18)

def ntree13RRRLRRLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1902,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 1 => ![⟨1903,by decide⟩,⟨1341,by decide⟩,⟨217,by decide⟩] | 2 => ![⟨1904,by decide⟩,⟨1342,by decide⟩,⟨218,by decide⟩] | _ => ![⟨1905,by decide⟩,⟨200,by decide⟩,⟨200,by decide⟩]

def ntree13RRRLRRLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1906,by decide⟩,⟨1343,by decide⟩,⟨8,by decide⟩] | 1 => ![⟨1907,by decide⟩,⟨1344,by decide⟩,⟨219,by decide⟩] | 2 => ![⟨1908,by decide⟩,⟨203,by decide⟩,⟨203,by decide⟩] | 3 => ![⟨1909,by decide⟩,⟨1311,by decide⟩,⟨221,by decide⟩] | _ => ![⟨1910,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13RRRLRRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13RRRLRRLLL i else ntree13RRRLRRLLR (i - 4)

def ntree13RRRLRRLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1911,by decide⟩,⟨1347,by decide⟩,⟨219,by decide⟩] | 1 => ![⟨1912,by decide⟩,⟨203,by decide⟩,⟨203,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1849,by decide⟩,⟨1913,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1897,by decide⟩,⟨1897,by decide⟩] | _ => ![⟨0,by decide⟩,⟨1104,by decide⟩,⟨1834,by decide⟩]

def ntree13RRRLRRLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1914,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1915,by decide⟩,⟨0,by decide⟩,⟨126,by decide⟩] | 2 => ![⟨1806,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1914,by decide⟩,⟨388,by decide⟩,⟨388,by decide⟩] | _ => ![⟨1880,by decide⟩,⟨1338,by decide⟩,⟨575,by decide⟩]

def ntree13RRRLRRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13RRRLRRLRL i else ntree13RRRLRRLRR (i - 5)

def ntree13RRRLRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13RRRLRRLL i else ntree13RRRLRRLR (i - 9)

def ntree13RRRLRRRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1806,by decide⟩,⟨1104,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1810,by decide⟩,⟨1363,by decide⟩,⟨8,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1916,by decide⟩,⟨1916,by decide⟩] | _ => ![⟨1917,by decide⟩,⟨1917,by decide⟩,⟨1668,by decide⟩]

def ntree13RRRLRRRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1918,by decide⟩,⟨1311,by decide⟩,⟨111,by decide⟩] | 1 => ![⟨1919,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1920,by decide⟩,⟨1347,by decide⟩,⟨260,by decide⟩] | 3 => ![⟨1921,by decide⟩,⟨203,by decide⟩,⟨203,by decide⟩] | _ => ![⟨1922,by decide⟩,⟨1311,by decide⟩,⟨269,by decide⟩]

def ntree13RRRLRRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13RRRLRRRLL i else ntree13RRRLRRRLR (i - 4)

def ntree13RRRLRRRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1923,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1924,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1925,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1925,by decide⟩,⟨526,by decide⟩,⟨1232,by decide⟩] | _ => ![⟨1311,by decide⟩,⟨1926,by decide⟩,⟨1927,by decide⟩]

def ntree13RRRLRRRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨1927,by decide⟩,⟨1927,by decide⟩] | 1 => ![⟨1928,by decide⟩,⟨1928,by decide⟩,⟨1607,by decide⟩] | 2 => ![⟨1929,by decide⟩,⟨1929,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1930,by decide⟩,⟨1930,by decide⟩,⟨1766,by decide⟩] | _ => ![⟨1931,by decide⟩,⟨1931,by decide⟩,⟨1688,by decide⟩]

def ntree13RRRLRRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13RRRLRRRRL i else ntree13RRRLRRRRR (i - 5)

def ntree13RRRLRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13RRRLRRRL i else ntree13RRRLRRRR (i - 9)

def ntree13RRRLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 19 then ntree13RRRLRRL i else ntree13RRRLRRR (i - 19)

def ntree13RRRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 37 then ntree13RRRLRL i else ntree13RRRLRR (i - 37)

def ntree13RRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 75 then ntree13RRRLL i else ntree13RRRLR (i - 75)

def ntree13RRRRLLLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1932,by decide⟩,⟨1929,by decide⟩,⟨126,by decide⟩] | 1 => ![⟨399,by decide⟩,⟨1933,by decide⟩,⟨1927,by decide⟩] | 2 => ![⟨1934,by decide⟩,⟨1928,by decide⟩,⟨1609,by decide⟩] | _ => ![⟨1935,by decide⟩,⟨1930,by decide⟩,⟨1770,by decide⟩]

def ntree13RRRRLLLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1936,by decide⟩,⟨1931,by decide⟩,⟨1692,by decide⟩] | 1 => ![⟨1937,by decide⟩,⟨1607,by decide⟩,⟨1607,by decide⟩] | 2 => ![⟨1938,by decide⟩,⟨1607,by decide⟩,⟨1607,by decide⟩] | 3 => ![⟨1939,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1940,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13RRRRLLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13RRRRLLLLL i else ntree13RRRRLLLLR (i - 4)

def ntree13RRRRLLLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1941,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1942,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1943,by decide⟩,⟨399,by decide⟩,⟨1171,by decide⟩]

def ntree13RRRRLLLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1930,by decide⟩,⟨1944,by decide⟩,⟨1945,by decide⟩] | 1 => ![⟨1766,by decide⟩,⟨1945,by decide⟩,⟨1945,by decide⟩] | 2 => ![⟨1311,by decide⟩,⟨1946,by decide⟩,⟨1947,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1947,by decide⟩,⟨1947,by decide⟩] | _ => ![⟨1311,by decide⟩,⟨1948,by decide⟩,⟨1949,by decide⟩]

def ntree13RRRRLLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13RRRRLLLRL i else ntree13RRRRLLLRR (i - 4)

def ntree13RRRRLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13RRRRLLLL i else ntree13RRRRLLLR (i - 9)

def ntree13RRRRLLRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨1950,by decide⟩,⟨1951,by decide⟩] | 1 => ![⟨977,by decide⟩,⟨1950,by decide⟩,⟨1952,by decide⟩] | 2 => ![⟨1923,by decide⟩,⟨439,by decide⟩,⟨1953,by decide⟩] | _ => ![⟨1925,by decide⟩,⟨439,by decide⟩,⟨1385,by decide⟩]

def ntree13RRRRLLRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1954,by decide⟩,⟨660,by decide⟩,⟨977,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1955,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1956,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1957,by decide⟩,⟨660,by decide⟩,⟨924,by decide⟩]

def ntree13RRRRLLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13RRRRLLRLL i else ntree13RRRRLLRLR (i - 4)

def ntree13RRRRLLRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨399,by decide⟩,⟨399,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1958,by decide⟩,⟨660,by decide⟩,⟨1115,by decide⟩] | 2 => ![⟨1959,by decide⟩,⟨203,by decide⟩,⟨203,by decide⟩] | 3 => ![⟨1960,by decide⟩,⟨675,by decide⟩,⟨1120,by decide⟩] | _ => ![⟨977,by decide⟩,⟨0,by decide⟩,⟨1961,by decide⟩]

def ntree13RRRRLLRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1962,by decide⟩,⟨1930,by decide⟩,⟨1786,by decide⟩] | 1 => ![⟨1963,by decide⟩,⟨1311,by decide⟩,⟨345,by decide⟩] | 2 => ![⟨1964,by decide⟩,⟨399,by decide⟩,⟨977,by decide⟩] | 3 => ![⟨1965,by decide⟩,⟨1311,by decide⟩,⟨346,by decide⟩] | _ => ![⟨1966,by decide⟩,⟨1347,by decide⟩,⟨347,by decide⟩]

def ntree13RRRRLLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13RRRRLLRRL i else ntree13RRRRLLRRR (i - 5)

def ntree13RRRRLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13RRRRLLRL i else ntree13RRRRLLRR (i - 9)

def ntree13RRRRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 18 then ntree13RRRRLLL i else ntree13RRRRLLR (i - 18)

def ntree13RRRRLRLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1967,by decide⟩,⟨203,by decide⟩,⟨203,by decide⟩] | 1 => ![⟨1968,by decide⟩,⟨399,by decide⟩,⟨977,by decide⟩] | 2 => ![⟨1969,by decide⟩,⟨203,by decide⟩,⟨203,by decide⟩] | _ => ![⟨1970,by decide⟩,⟨675,by decide⟩,⟨1207,by decide⟩]

def ntree13RRRRLRLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1971,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1972,by decide⟩,⟨399,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1973,by decide⟩,⟨1974,by decide⟩,⟨1975,by decide⟩] | 3 => ![⟨1976,by decide⟩,⟨1977,by decide⟩,⟨1978,by decide⟩] | _ => ![⟨126,by decide⟩,⟨1950,by decide⟩,⟨1979,by decide⟩]

def ntree13RRRRLRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13RRRRLRLLL i else ntree13RRRRLRLLR (i - 4)

def ntree13RRRRLRLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1980,by decide⟩,⟨1981,by decide⟩,⟨1982,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1983,by decide⟩,⟨1916,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1984,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1311,by decide⟩,⟨1311,by decide⟩,⟨503,by decide⟩] | _ => ![⟨1819,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13RRRRLRLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1971,by decide⟩,⟨388,by decide⟩,⟨388,by decide⟩] | 1 => ![⟨1985,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1986,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨1985,by decide⟩,⟨1986,by decide⟩,⟨1232,by decide⟩] | _ => ![⟨1987,by decide⟩,⟨1988,by decide⟩,⟨1989,by decide⟩]

def ntree13RRRRLRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13RRRRLRLRL i else ntree13RRRRLRLRR (i - 5)

def ntree13RRRRLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13RRRRLRLL i else ntree13RRRRLRLR (i - 9)

def ntree13RRRRLRRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1990,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1991,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1990,by decide⟩,⟨1991,by decide⟩,⟨16,by decide⟩] | _ => ![⟨1992,by decide⟩,⟨1993,by decide⟩,⟨1994,by decide⟩]

def ntree13RRRRLRRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1995,by decide⟩,⟨1996,by decide⟩,⟨1997,by decide⟩] | 1 => ![⟨1998,by decide⟩,⟨1998,by decide⟩,⟨1998,by decide⟩] | 2 => ![⟨935,by decide⟩,⟨1999,by decide⟩,⟨1814,by decide⟩] | 3 => ![⟨2000,by decide⟩,⟨2001,by decide⟩,⟨2002,by decide⟩] | _ => ![⟨2003,by decide⟩,⟨935,by decide⟩,⟨720,by decide⟩]

def ntree13RRRRLRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13RRRRLRRLL i else ntree13RRRRLRRLR (i - 4)

def ntree13RRRRLRRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨2004,by decide⟩,⟨2005,by decide⟩,⟨2006,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨2007,by decide⟩,⟨2008,by decide⟩,⟨2009,by decide⟩]

def ntree13RRRRLRRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨2010,by decide⟩,⟨399,by decide⟩,⟨1428,by decide⟩] | 1 => ![⟨2011,by decide⟩,⟨2012,by decide⟩,⟨2013,by decide⟩] | 2 => ![⟨399,by decide⟩,⟨2014,by decide⟩,⟨1622,by decide⟩] | 3 => ![⟨2015,by decide⟩,⟨2016,by decide⟩,⟨2017,by decide⟩] | _ => ![⟨2018,by decide⟩,⟨2019,by decide⟩,⟨2020,by decide⟩]

def ntree13RRRRLRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13RRRRLRRRL i else ntree13RRRRLRRRR (i - 5)

def ntree13RRRRLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13RRRRLRRL i else ntree13RRRRLRRR (i - 9)

def ntree13RRRRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 19 then ntree13RRRRLRL i else ntree13RRRRLRR (i - 19)

def ntree13RRRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 37 then ntree13RRRRLL i else ntree13RRRRLR (i - 37)

def ntree13RRRRRLLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨2021,by decide⟩,⟨65,by decide⟩,⟨984,by decide⟩] | 1 => ![⟨1441,by decide⟩,⟨1831,by decide⟩,⟨2022,by decide⟩] | 2 => ![⟨2023,by decide⟩,⟨384,by decide⟩,⟨1441,by decide⟩] | _ => ![⟨995,by decide⟩,⟨713,by decide⟩,⟨995,by decide⟩]

def ntree13RRRRRLLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1832,by decide⟩,⟨714,by decide⟩,⟨997,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨713,by decide⟩,⟨1001,by decide⟩] | 2 => ![⟨2024,by decide⟩,⟨65,by decide⟩,⟨1453,by decide⟩] | 3 => ![⟨2025,by decide⟩,⟨746,by decide⟩,⟨1455,by decide⟩] | _ => ![⟨2026,by decide⟩,⟨747,by decide⟩,⟨747,by decide⟩]

def ntree13RRRRRLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13RRRRRLLLL i else ntree13RRRRRLLLR (i - 4)

def ntree13RRRRRLLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨399,by decide⟩,⟨399,by decide⟩,⟨1001,by decide⟩] | 1 => ![⟨1985,by decide⟩,⟨0,by decide⟩,⟨1001,by decide⟩] | 2 => ![⟨65,by decide⟩,⟨2027,by decide⟩,⟨1849,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13RRRRRLLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨65,by decide⟩,⟨2028,by decide⟩,⟨490,by decide⟩] | 2 => ![⟨921,by decide⟩,⟨2029,by decide⟩,⟨1831,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨1986,by decide⟩,⟨503,by decide⟩] | _ => ![⟨935,by decide⟩,⟨935,by decide⟩,⟨503,by decide⟩]

def ntree13RRRRRLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13RRRRRLLRL i else ntree13RRRRRLLRR (i - 4)

def ntree13RRRRRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13RRRRRLLL i else ntree13RRRRRLLR (i - 9)

def ntree13RRRRRLRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1613,by decide⟩,⟨515,by decide⟩,⟨515,by decide⟩] | _ => ![⟨1615,by decide⟩,⟨1479,by decide⟩,⟨517,by decide⟩]

def ntree13RRRRRLRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1613,by decide⟩,⟨0,by decide⟩,⟨503,by decide⟩] | 1 => ![⟨1667,by decide⟩,⟨2030,by decide⟩,⟨1870,by decide⟩] | 2 => ![⟨1668,by decide⟩,⟨2031,by decide⟩,⟨1668,by decide⟩] | 3 => ![⟨2032,by decide⟩,⟨921,by decide⟩,⟨790,by decide⟩] | _ => ![⟨790,by decide⟩,⟨1689,by decide⟩,⟨2033,by decide⟩]

def ntree13RRRRRLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13RRRRRLRLL i else ntree13RRRRRLRLR (i - 4)

def ntree13RRRRRLRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨2034,by decide⟩,⟨1311,by decide⟩,⟨134,by decide⟩] | 1 => ![⟨935,by decide⟩,⟨935,by decide⟩,⟨536,by decide⟩] | 2 => ![⟨1311,by decide⟩,⟨2035,by decide⟩,⟨1695,by decide⟩] | 3 => ![⟨1990,by decide⟩,⟨0,by decide⟩,⟨536,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13RRRRRLRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨2036,by decide⟩,⟨1311,by decide⟩,⟨811,by decide⟩] | 2 => ![⟨2037,by decide⟩,⟨1494,by decide⟩,⟨813,by decide⟩] | 3 => ![⟨2038,by decide⟩,⟨802,by decide⟩,⟨802,by decide⟩] | _ => ![⟨169,by decide⟩,⟨1431,by decide⟩,⟨169,by decide⟩]

def ntree13RRRRRLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13RRRRRLRRL i else ntree13RRRRRLRRR (i - 5)

def ntree13RRRRRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13RRRRRLRL i else ntree13RRRRRLRR (i - 9)

def ntree13RRRRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 18 then ntree13RRRRRLL i else ntree13RRRRRLR (i - 18)

def ntree13RRRRRRLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1713,by decide⟩,⟨1432,by decide⟩,⟨551,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨1431,by decide⟩,⟨536,by decide⟩] | 2 => ![⟨2039,by decide⟩,⟨2039,by decide⟩,⟨2040,by decide⟩] | _ => ![⟨2041,by decide⟩,⟨2039,by decide⟩,⟨2042,by decide⟩]

def ntree13RRRRRRLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨2043,by decide⟩,⟨65,by decide⟩,⟨2044,by decide⟩] | 1 => ![⟨2045,by decide⟩,⟨2039,by decide⟩,⟨2046,by decide⟩] | 2 => ![⟨2047,by decide⟩,⟨1311,by decide⟩,⟨2048,by decide⟩] | 3 => ![⟨2049,by decide⟩,⟨2050,by decide⟩,⟨2051,by decide⟩] | _ => ![⟨2052,by decide⟩,⟨2053,by decide⟩,⟨2054,by decide⟩]

def ntree13RRRRRRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13RRRRRRLLL i else ntree13RRRRRRLLR (i - 4)

def ntree13RRRRRRLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨2055,by decide⟩,⟨2056,by decide⟩,⟨2057,by decide⟩] | 1 => ![⟨2039,by decide⟩,⟨2039,by decide⟩,⟨2058,by decide⟩] | 2 => ![⟨1311,by decide⟩,⟨2035,by decide⟩,⟨1719,by decide⟩] | 3 => ![⟨65,by decide⟩,⟨2027,by decide⟩,⟨1913,by decide⟩] | _ => ![⟨2039,by decide⟩,⟨2059,by decide⟩,⟨2060,by decide⟩]

def ntree13RRRRRRLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1311,by decide⟩,⟨2061,by decide⟩,⟨2062,by decide⟩] | 1 => ![⟨2063,by decide⟩,⟨2063,by decide⟩,⟨2064,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨384,by decide⟩,⟨2065,by decide⟩,⟨1689,by decide⟩] | _ => ![⟨1311,by decide⟩,⟨2066,by decide⟩,⟨279,by decide⟩]

def ntree13RRRRRRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13RRRRRRLRL i else ntree13RRRRRRLRR (i - 5)

def ntree13RRRRRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13RRRRRRLL i else ntree13RRRRRRLR (i - 9)

def ntree13RRRRRRRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨399,by decide⟩,⟨399,by decide⟩,⟨1165,by decide⟩] | 1 => ![⟨1930,by decide⟩,⟨2067,by decide⟩,⟨1767,by decide⟩] | 2 => ![⟨1766,by decide⟩,⟨2068,by decide⟩,⟨1766,by decide⟩] | _ => ![⟨1819,by decide⟩,⟨298,by decide⟩,⟨298,by decide⟩]

def ntree13RRRRRRRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1821,by decide⟩,⟨862,by decide⟩,⟨1168,by decide⟩] | 1 => ![⟨1819,by decide⟩,⟨0,by decide⟩,⟨1165,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨1991,by decide⟩,⟨1165,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13RRRRRRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13RRRRRRRLL i else ntree13RRRRRRRLR (i - 4)

def ntree13RRRRRRRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨2039,by decide⟩,⟨2069,by decide⟩,⟨2070,by decide⟩] | 1 => ![⟨65,by decide⟩,⟨2071,by decide⟩,⟨2072,by decide⟩] | 2 => ![⟨2073,by decide⟩,⟨2073,by decide⟩,⟨2074,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨2075,by decide⟩,⟨2076,by decide⟩,⟨2077,by decide⟩]

def ntree13RRRRRRRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨2078,by decide⟩,⟨2079,by decide⟩,⟨2080,by decide⟩] | 1 => ![⟨2081,by decide⟩,⟨2082,by decide⟩,⟨2083,by decide⟩] | 2 => ![⟨2039,by decide⟩,⟨2039,by decide⟩,⟨2084,by decide⟩] | 3 => ![⟨2024,by decide⟩,⟨65,by decide⟩,⟨1592,by decide⟩] | _ => ![⟨2036,by decide⟩,⟨1311,by decide⟩,⟨897,by decide⟩]

def ntree13RRRRRRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13RRRRRRRRL i else ntree13RRRRRRRRR (i - 5)

def ntree13RRRRRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13RRRRRRRL i else ntree13RRRRRRRR (i - 9)

def ntree13RRRRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 19 then ntree13RRRRRRL i else ntree13RRRRRRR (i - 19)

def ntree13RRRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 37 then ntree13RRRRRL i else ntree13RRRRRR (i - 37)

def ntree13RRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 75 then ntree13RRRRL i else ntree13RRRRR (i - 75)

def ntree13RRR (i : Nat) : Fin 3 → Fin 2085 := if i < 150 then ntree13RRRL i else ntree13RRRR (i - 150)

def ntree13RR (i : Nat) : Fin 3 → Fin 2085 := if i < 299 then ntree13RRL i else ntree13RRR (i - 299)

def ntree13R (i : Nat) : Fin 3 → Fin 2085 := if i < 599 then ntree13RL i else ntree13RR (i - 599)

def ntree13 (i : Nat) : Fin 3 → Fin 2085 := if i < 1198 then ntree13L i else ntree13R (i - 1198)

def layer13 : Fin 2085 → State := fun i => stree13 i.val

def next13 : Fin 2396 → Fin 3 → Fin 2085 := fun i => ntree13 i.val

end Paper2.Certificates.Q6.Coverage
