import Paper2.Certificates.Q6CoverageCompact.Layer08Part008

namespace Paper2.Certificates.Q6.Coverage

def ntree8RLLLLRL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLLLLRLL i else ntree8RLLLLRLR (i - 7)

def ntree8RLLLLRRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1824,by decide⟩,⟨1825,by decide⟩,⟨1429,by decide⟩] | 1 => ![⟨1786,by decide⟩,⟨1826,by decide⟩,⟨1827,by decide⟩] | 2 => ![⟨1778,by decide⟩,⟨1828,by decide⟩,⟨1829,by decide⟩] | 3 => ![⟨1795,by decide⟩,⟨1830,by decide⟩,⟨1435,by decide⟩] | 4 => ![⟨1831,by decide⟩,⟨1832,by decide⟩,⟨1833,by decide⟩] | 5 => ![⟨1819,by decide⟩,⟨1834,by decide⟩,⟨1441,by decide⟩] | _ => ![⟨1835,by decide⟩,⟨1834,by decide⟩,⟨1442,by decide⟩]

def ntree8RLLLLRRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1836,by decide⟩,⟨1837,by decide⟩,⟨1838,by decide⟩] | 1 => ![⟨1839,by decide⟩,⟨1840,by decide⟩,⟨1449,by decide⟩] | 2 => ![⟨1767,by decide⟩,⟨1841,by decide⟩,⟨1842,by decide⟩] | 3 => ![⟨1790,by decide⟩,⟨1843,by decide⟩,⟨213,by decide⟩] | 4 => ![⟨1831,by decide⟩,⟨1817,by decide⟩,⟨1844,by decide⟩] | 5 => ![⟨1845,by decide⟩,⟨1846,by decide⟩,⟨1458,by decide⟩] | _ => ![⟨1847,by decide⟩,⟨1846,by decide⟩,⟨1459,by decide⟩]

def ntree8RLLLLRR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLLLLRRL i else ntree8RLLLLRRR (i - 7)

def ntree8RLLLLR (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RLLLLRL i else ntree8RLLLLRR (i - 14)

def ntree8RLLLL (i : Nat) : Fin 3 → Fin 3321 := if i < 28 then ntree8RLLLLL i else ntree8RLLLLR (i - 28)

def ntree8RLLLRLLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1848,by decide⟩,⟨1849,by decide⟩,⟨1850,by decide⟩] | 1 => ![⟨1851,by decide⟩,⟨1814,by decide⟩,⟨1852,by decide⟩] | 2 => ![⟨1782,by decide⟩,⟨1853,by decide⟩,⟨1854,by decide⟩] | 3 => ![⟨1855,by decide⟩,⟨1856,by decide⟩,⟨1857,by decide⟩] | 4 => ![⟨1782,by decide⟩,⟨1858,by decide⟩,⟨689,by decide⟩] | 5 => ![⟨1859,by decide⟩,⟨1814,by decide⟩,⟨1860,by decide⟩] | _ => ![⟨1861,by decide⟩,⟨1862,by decide⟩,⟨1863,by decide⟩]

def ntree8RLLLRLLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1864,by decide⟩,⟨1865,by decide⟩,⟨1866,by decide⟩] | 1 => ![⟨1867,by decide⟩,⟨1825,by decide⟩,⟨1868,by decide⟩] | 2 => ![⟨1790,by decide⟩,⟨1869,by decide⟩,⟨1692,by decide⟩] | 3 => ![⟨1856,by decide⟩,⟨1870,by decide⟩,⟨1871,by decide⟩] | 4 => ![⟨1872,by decide⟩,⟨1825,by decide⟩,⟨1873,by decide⟩] | 5 => ![⟨1874,by decide⟩,⟨1875,by decide⟩,⟨1876,by decide⟩] | _ => ![⟨1877,by decide⟩,⟨1878,by decide⟩,⟨1879,by decide⟩]

def ntree8RLLLRLL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLLLRLLL i else ntree8RLLLRLLR (i - 7)

def ntree8RLLLRLRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1880,by decide⟩,⟨1840,by decide⟩,⟨1881,by decide⟩] | 1 => ![⟨1782,by decide⟩,⟨1843,by decide⟩,⟨716,by decide⟩] | 2 => ![⟨1805,by decide⟩,⟨1882,by decide⟩,⟨718,by decide⟩] | 3 => ![⟨1883,by decide⟩,⟨1840,by decide⟩,⟨1884,by decide⟩] | 4 => ![⟨1885,by decide⟩,⟨1886,by decide⟩,⟨1887,by decide⟩] | 5 => ![⟨1888,by decide⟩,⟨1889,by decide⟩,⟨726,by decide⟩] | _ => ![⟨1890,by decide⟩,⟨1889,by decide⟩,⟨1891,by decide⟩]

def ntree8RLLLRLRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1890,by decide⟩,⟨1888,by decide⟩,⟨1633,by decide⟩] | 1 => ![⟨1892,by decide⟩,⟨1888,by decide⟩,⟨424,by decide⟩] | 2 => ![⟨1893,by decide⟩,⟨1894,by decide⟩,⟨1637,by decide⟩] | 3 => ![⟨1782,by decide⟩,⟨1895,by decide⟩,⟨738,by decide⟩] | 4 => ![⟨1780,by decide⟩,⟨1896,by decide⟩,⟨1897,by decide⟩] | 5 => ![⟨1898,by decide⟩,⟨1899,by decide⟩,⟨743,by decide⟩] | _ => ![⟨1888,by decide⟩,⟨1899,by decide⟩,⟨1900,by decide⟩]

def ntree8RLLLRLR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLLLRLRL i else ntree8RLLLRLRR (i - 7)

def ntree8RLLLRL (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RLLLRLL i else ntree8RLLLRLR (i - 14)

def ntree8RLLLRRLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1898,by decide⟩,⟨1888,by decide⟩,⟨28,by decide⟩] | 1 => ![⟨1894,by decide⟩,⟨1894,by decide⟩,⟨1206,by decide⟩] | 2 => ![⟨1901,by decide⟩,⟨1894,by decide⟩,⟨1224,by decide⟩] | 3 => ![⟨1790,by decide⟩,⟨1902,by decide⟩,⟨751,by decide⟩] | 4 => ![⟨1781,by decide⟩,⟨1903,by decide⟩,⟨1904,by decide⟩] | 5 => ![⟨1898,by decide⟩,⟨1889,by decide⟩,⟨754,by decide⟩] | _ => ![⟨1888,by decide⟩,⟨1889,by decide⟩,⟨1905,by decide⟩]

def ntree8RLLLRRLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1906,by decide⟩,⟨1907,by decide⟩,⟨455,by decide⟩] | 1 => ![⟨1805,by decide⟩,⟨1908,by decide⟩,⟨763,by decide⟩] | 2 => ![⟨1782,by decide⟩,⟨1909,by decide⟩,⟨1910,by decide⟩] | 3 => ![⟨1911,by decide⟩,⟨1912,by decide⟩,⟨1913,by decide⟩] | 4 => ![⟨1914,by decide⟩,⟨1915,by decide⟩,⟨1916,by decide⟩] | 5 => ![⟨1917,by decide⟩,⟨1918,by decide⟩,⟨1919,by decide⟩] | _ => ![⟨1920,by decide⟩,⟨1921,by decide⟩,⟨1922,by decide⟩]

def ntree8RLLLRRL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLLLRRLL i else ntree8RLLLRRLR (i - 7)

def ntree8RLLLRRRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1923,by decide⟩,⟨1781,by decide⟩,⟨1674,by decide⟩] | 1 => ![⟨1923,by decide⟩,⟨1924,by decide⟩,⟨1925,by decide⟩] | 2 => ![⟨1911,by decide⟩,⟨1926,by decide⟩,⟨1927,by decide⟩] | 3 => ![⟨1928,by decide⟩,⟨1781,by decide⟩,⟨1929,by decide⟩] | 4 => ![⟨1930,by decide⟩,⟨1931,by decide⟩,⟨1932,by decide⟩] | 5 => ![⟨1933,by decide⟩,⟨1934,by decide⟩,⟨1935,by decide⟩] | _ => ![⟨1790,by decide⟩,⟨1936,by decide⟩,⟨1937,by decide⟩]

def ntree8RLLLRRRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1781,by decide⟩,⟨1830,by decide⟩,⟨1581,by decide⟩] | 1 => ![⟨1930,by decide⟩,⟨1938,by decide⟩,⟨1939,by decide⟩] | 2 => ![⟨1940,by decide⟩,⟨1830,by decide⟩,⟨1941,by decide⟩] | 3 => ![⟨1942,by decide⟩,⟨1943,by decide⟩,⟨1944,by decide⟩] | 4 => ![⟨1945,by decide⟩,⟨1946,by decide⟩,⟨1947,by decide⟩] | 5 => ![⟨1948,by decide⟩,⟨1949,by decide⟩,⟨518,by decide⟩] | 6 => ![⟨1920,by decide⟩,⟨1843,by decide⟩,⟨1950,by decide⟩] | _ => ![⟨1948,by decide⟩,⟨1951,by decide⟩,⟨1952,by decide⟩]

def ntree8RLLLRRR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLLLRRRL i else ntree8RLLLRRRR (i - 7)

def ntree8RLLLRR (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RLLLRRL i else ntree8RLLLRRR (i - 14)

def ntree8RLLLR (i : Nat) : Fin 3 → Fin 3321 := if i < 28 then ntree8RLLLRL i else ntree8RLLLRR (i - 28)

def ntree8RLLL (i : Nat) : Fin 3 → Fin 3321 := if i < 56 then ntree8RLLLL i else ntree8RLLLR (i - 56)

def ntree8RLLRLLLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1942,by decide⟩,⟨1953,by decide⟩,⟨1954,by decide⟩] | 1 => ![⟨1955,by decide⟩,⟨1843,by decide⟩,⟨1956,by decide⟩] | 2 => ![⟨1957,by decide⟩,⟨1958,by decide⟩,⟨1720,by decide⟩] | 3 => ![⟨1959,by decide⟩,⟨1888,by decide⟩,⟨1960,by decide⟩] | 4 => ![⟨1888,by decide⟩,⟨1888,by decide⟩,⟨393,by decide⟩] | 5 => ![⟨1892,by decide⟩,⟨1961,by decide⟩,⟨833,by decide⟩] | _ => ![⟨1962,by decide⟩,⟨1963,by decide⟩,⟨1731,by decide⟩]

def ntree8RLLRLLLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1964,by decide⟩,⟨1965,by decide⟩,⟨1966,by decide⟩] | 1 => ![⟨1967,by decide⟩,⟨1958,by decide⟩,⟨1738,by decide⟩] | 2 => ![⟨1968,by decide⟩,⟨1969,by decide⟩,⟨1970,by decide⟩] | 3 => ![⟨1898,by decide⟩,⟨1969,by decide⟩,⟨406,by decide⟩] | 4 => ![⟨1888,by decide⟩,⟨1969,by decide⟩,⟨411,by decide⟩] | 5 => ![⟨1971,by decide⟩,⟨1963,by decide⟩,⟨1748,by decide⟩] | _ => ![⟨1972,by decide⟩,⟨1973,by decide⟩,⟨1974,by decide⟩]

def ntree8RLLRLLL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLLRLLLL i else ntree8RLLRLLLR (i - 7)

def ntree8RLLRLLRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1975,by decide⟩,⟨1976,by decide⟩,⟨1755,by decide⟩] | 1 => ![⟨1959,by decide⟩,⟨1969,by decide⟩,⟨1977,by decide⟩] | 2 => ![⟨1892,by decide⟩,⟨1969,by decide⟩,⟨851,by decide⟩] | 3 => ![⟨1906,by decide⟩,⟨1978,by decide⟩,⟨853,by decide⟩] | 4 => ![⟨1979,by decide⟩,⟨1980,by decide⟩,⟨1761,by decide⟩] | 5 => ![⟨1964,by decide⟩,⟨1973,by decide⟩,⟨1981,by decide⟩] | _ => ![⟨6,by decide⟩,⟨1201,by decide⟩,⟨1201,by decide⟩]

def ntree8RLLRLLRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1633,by decide⟩,⟨1982,by decide⟩,⟨1632,by decide⟩] | 1 => ![⟨1983,by decide⟩,⟨1201,by decide⟩,⟨1984,by decide⟩] | 2 => ![⟨424,by decide⟩,⟨1985,by decide⟩,⟨1986,by decide⟩] | 3 => ![⟨1637,by decide⟩,⟨1987,by decide⟩,⟨1637,by decide⟩] | 4 => ![⟨1637,by decide⟩,⟨1207,by decide⟩,⟨1988,by decide⟩] | 5 => ![⟨863,by decide⟩,⟨1989,by decide⟩,⟨1990,by decide⟩] | _ => ![⟨1642,by decide⟩,⟨1991,by decide⟩,⟨1641,by decide⟩]

def ntree8RLLRLLR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLLRLLRL i else ntree8RLLRLLRR (i - 7)

def ntree8RLLRLL (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RLLRLLL i else ntree8RLLRLLR (i - 14)

def ntree8RLLRLRLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1992,by decide⟩,⟨1215,by decide⟩,⟨1993,by decide⟩] | 1 => ![⟨869,by decide⟩,⟨1221,by decide⟩,⟨1221,by decide⟩] | 2 => ![⟨1994,by decide⟩,⟨1995,by decide⟩,⟨1646,by decide⟩] | 3 => ![⟨6,by decide⟩,⟨1221,by decide⟩,⟨1996,by decide⟩] | 4 => ![⟨874,by decide⟩,⟨1997,by decide⟩,⟨1998,by decide⟩] | 5 => ![⟨1206,by decide⟩,⟨1999,by decide⟩,⟨1206,by decide⟩] | _ => ![⟨1206,by decide⟩,⟨1225,by decide⟩,⟨2000,by decide⟩]

def ntree8RLLRLRLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨879,by decide⟩,⟨2001,by decide⟩,⟨2002,by decide⟩] | 1 => ![⟨1378,by decide⟩,⟨2003,by decide⟩,⟨1651,by decide⟩] | 2 => ![⟨1214,by decide⟩,⟨1233,by decide⟩,⟨2004,by decide⟩] | 3 => ![⟨874,by decide⟩,⟨1237,by decide⟩,⟨1237,by decide⟩] | 4 => ![⟨2005,by decide⟩,⟨2006,by decide⟩,⟨1655,by decide⟩] | 5 => ![⟨2007,by decide⟩,⟨1237,by decide⟩,⟨2008,by decide⟩] | _ => ![⟨890,by decide⟩,⟨2009,by decide⟩,⟨2010,by decide⟩]

def ntree8RLLRLRL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLLRLRLL i else ntree8RLLRLRLR (i - 7)

def ntree8RLLRLRRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨424,by decide⟩,⟨2011,by decide⟩,⟨424,by decide⟩] | 1 => ![⟨424,by decide⟩,⟨1239,by decide⟩,⟨2012,by decide⟩] | 2 => ![⟨894,by decide⟩,⟨2013,by decide⟩,⟨2014,by decide⟩] | 3 => ![⟨2015,by decide⟩,⟨2016,by decide⟩,⟨1659,by decide⟩] | 4 => ![⟨2017,by decide⟩,⟨1247,by decide⟩,⟨2018,by decide⟩] | 5 => ![⟨2019,by decide⟩,⟨1266,by decide⟩,⟨1266,by decide⟩] | _ => ![⟨2020,by decide⟩,⟨2021,by decide⟩,⟨2022,by decide⟩]

def ntree8RLLRLRRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2023,by decide⟩,⟨2024,by decide⟩,⟨2025,by decide⟩] | 1 => ![⟨2026,by decide⟩,⟨2027,by decide⟩,⟨2028,by decide⟩] | 2 => ![⟨2029,by decide⟩,⟨2030,by decide⟩,⟨2029,by decide⟩] | 3 => ![⟨2031,by decide⟩,⟨2032,by decide⟩,⟨2033,by decide⟩] | 4 => ![⟨2034,by decide⟩,⟨2035,by decide⟩,⟨1266,by decide⟩] | 5 => ![⟨2036,by decide⟩,⟨2037,by decide⟩,⟨1268,by decide⟩] | _ => ![⟨2038,by decide⟩,⟨2039,by decide⟩,⟨1215,by decide⟩]

def ntree8RLLRLRR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLLRLRRL i else ntree8RLLRLRRR (i - 7)

def ntree8RLLRLR (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RLLRLRL i else ntree8RLLRLRR (i - 14)

def ntree8RLLRL (i : Nat) : Fin 3 → Fin 3321 := if i < 28 then ntree8RLLRLL i else ntree8RLLRLR (i - 28)

def ntree8RLLRRLLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2040,by decide⟩,⟨1285,by decide⟩,⟨1285,by decide⟩] | 1 => ![⟨2041,by decide⟩,⟨2042,by decide⟩,⟨2043,by decide⟩] | 2 => ![⟨2044,by decide⟩,⟨2045,by decide⟩,⟨2046,by decide⟩] | 3 => ![⟨2047,by decide⟩,⟨2048,by decide⟩,⟨2049,by decide⟩] | 4 => ![⟨2050,by decide⟩,⟨2051,by decide⟩,⟨2050,by decide⟩] | 5 => ![⟨2052,by decide⟩,⟨2053,by decide⟩,⟨2054,by decide⟩] | _ => ![⟨2034,by decide⟩,⟨2055,by decide⟩,⟨1285,by decide⟩]

def ntree8RLLRRLLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2036,by decide⟩,⟨2056,by decide⟩,⟨1287,by decide⟩] | 1 => ![⟨2038,by decide⟩,⟨2057,by decide⟩,⟨1233,by decide⟩] | 2 => ![⟨2058,by decide⟩,⟨1300,by decide⟩,⟨1300,by decide⟩] | 3 => ![⟨2059,by decide⟩,⟨2060,by decide⟩,⟨2061,by decide⟩] | 4 => ![⟨2062,by decide⟩,⟨2063,by decide⟩,⟨2064,by decide⟩] | 5 => ![⟨2065,by decide⟩,⟨2066,by decide⟩,⟨2067,by decide⟩] | _ => ![⟨2068,by decide⟩,⟨2069,by decide⟩,⟨2068,by decide⟩]

def ntree8RLLRRLL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLLRRLLL i else ntree8RLLRRLLR (i - 7)

def ntree8RLLRRLRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2070,by decide⟩,⟨2071,by decide⟩,⟨2072,by decide⟩] | 1 => ![⟨2073,by decide⟩,⟨2074,by decide⟩,⟨1300,by decide⟩] | 2 => ![⟨2075,by decide⟩,⟨2076,by decide⟩,⟨1302,by decide⟩] | 3 => ![⟨2077,by decide⟩,⟨2078,by decide⟩,⟨1247,by decide⟩] | 4 => ![⟨1603,by decide⟩,⟨1305,by decide⟩,⟨1305,by decide⟩] | 5 => ![⟨2079,by decide⟩,⟨2080,by decide⟩,⟨1308,by decide⟩] | _ => ![⟨954,by decide⟩,⟨2081,by decide⟩,⟨1201,by decide⟩]

def ntree8RLLRRLRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2082,by decide⟩,⟨1311,by decide⟩,⟨2083,by decide⟩] | 1 => ![⟨2082,by decide⟩,⟨2084,by decide⟩,⟨2082,by decide⟩] | 2 => ![⟨959,by decide⟩,⟨2085,by decide⟩,⟨1986,by decide⟩] | 3 => ![⟨2086,by decide⟩,⟨1266,by decide⟩,⟨2087,by decide⟩] | 4 => ![⟨2088,by decide⟩,⟨2021,by decide⟩,⟨2089,by decide⟩] | 5 => ![⟨965,by decide⟩,⟨2024,by decide⟩,⟨1990,by decide⟩] | _ => ![⟨1603,by decide⟩,⟨1320,by decide⟩,⟨1320,by decide⟩]

def ntree8RLLRRLR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLLRRLRL i else ntree8RLLRRLRR (i - 7)

def ntree8RLLRRL (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RLLRRLL i else ntree8RLLRRLR (i - 14)

def ntree8RLLRRRLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2079,by decide⟩,⟨2090,by decide⟩,⟨1323,by decide⟩] | 1 => ![⟨954,by decide⟩,⟨2091,by decide⟩,⟨1221,by decide⟩] | 2 => ![⟨2092,by decide⟩,⟨1326,by decide⟩,⟨2093,by decide⟩] | 3 => ![⟨2092,by decide⟩,⟨2094,by decide⟩,⟨2092,by decide⟩] | 4 => ![⟨970,by decide⟩,⟨2095,by decide⟩,⟨1998,by decide⟩] | 5 => ![⟨2096,by decide⟩,⟨1285,by decide⟩,⟨2097,by decide⟩] | _ => ![⟨2098,by decide⟩,⟨2042,by decide⟩,⟨2099,by decide⟩]

def ntree8RLLRRRLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨975,by decide⟩,⟨2045,by decide⟩,⟨2002,by decide⟩] | 1 => ![⟨1622,by decide⟩,⟨1333,by decide⟩,⟨1333,by decide⟩] | 2 => ![⟨2100,by decide⟩,⟨2101,by decide⟩,⟨1308,by decide⟩] | 3 => ![⟨978,by decide⟩,⟨2102,by decide⟩,⟨1237,by decide⟩] | 4 => ![⟨2082,by decide⟩,⟨1326,by decide⟩,⟨2103,by decide⟩] | 5 => ![⟨2082,by decide⟩,⟨2094,by decide⟩,⟨2082,by decide⟩] | _ => ![⟨959,by decide⟩,⟨2095,by decide⟩,⟨2010,by decide⟩]

def ntree8RLLRRRL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLLRRRLL i else ntree8RLLRRRLR (i - 7)

def ntree8RLLRRRRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2104,by decide⟩,⟨1300,by decide⟩,⟨2105,by decide⟩] | 1 => ![⟨2106,by decide⟩,⟨2060,by decide⟩,⟨2089,by decide⟩] | 2 => ![⟨982,by decide⟩,⟨2063,by decide⟩,⟨2014,by decide⟩] | 3 => ![⟨2107,by decide⟩,⟨2108,by decide⟩,⟨2109,by decide⟩] | 4 => ![⟨1772,by decide⟩,⟨2110,by decide⟩,⟨2111,by decide⟩] | 5 => ![⟨2112,by decide⟩,⟨2108,by decide⟩,⟨2113,by decide⟩] | _ => ![⟨1782,by decide⟩,⟨2114,by decide⟩,⟨2115,by decide⟩]

def ntree8RLLRRRRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1780,by decide⟩,⟨2116,by decide⟩,⟨2117,by decide⟩] | 1 => ![⟨1780,by decide⟩,⟨2118,by decide⟩,⟨2119,by decide⟩] | 2 => ![⟨1782,by decide⟩,⟨2120,by decide⟩,⟨2121,by decide⟩] | 3 => ![⟨1780,by decide⟩,⟨2122,by decide⟩,⟨2123,by decide⟩] | 4 => ![⟨2124,by decide⟩,⟨2125,by decide⟩,⟨2126,by decide⟩] | 5 => ![⟨2127,by decide⟩,⟨2128,by decide⟩,⟨2129,by decide⟩] | 6 => ![⟨2107,by decide⟩,⟨2125,by decide⟩,⟨2130,by decide⟩] | _ => ![⟨2131,by decide⟩,⟨2132,by decide⟩,⟨2133,by decide⟩]

def ntree8RLLRRRR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLLRRRRL i else ntree8RLLRRRRR (i - 7)

def ntree8RLLRRR (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RLLRRRL i else ntree8RLLRRRR (i - 14)

def ntree8RLLRR (i : Nat) : Fin 3 → Fin 3321 := if i < 28 then ntree8RLLRRL i else ntree8RLLRRR (i - 28)

def ntree8RLLR (i : Nat) : Fin 3 → Fin 3321 := if i < 56 then ntree8RLLRL i else ntree8RLLRR (i - 56)

def ntree8RLL (i : Nat) : Fin 3 → Fin 3321 := if i < 113 then ntree8RLLL i else ntree8RLLR (i - 113)

def ntree8RLRLLLLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1781,by decide⟩,⟨2134,by decide⟩,⟨2135,by decide⟩] | 1 => ![⟨1781,by decide⟩,⟨2136,by decide⟩,⟨2137,by decide⟩] | 2 => ![⟨2127,by decide⟩,⟨2138,by decide⟩,⟨2139,by decide⟩] | 3 => ![⟨2140,by decide⟩,⟨2141,by decide⟩,⟨2142,by decide⟩] | 4 => ![⟨2131,by decide⟩,⟨2143,by decide⟩,⟨2144,by decide⟩] | 5 => ![⟨2145,by decide⟩,⟨2146,by decide⟩,⟨2147,by decide⟩] | _ => ![⟨2148,by decide⟩,⟨2143,by decide⟩,⟨2149,by decide⟩]

def ntree8RLRLLLLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2150,by decide⟩,⟨2151,by decide⟩,⟨2152,by decide⟩] | 1 => ![⟨1782,by decide⟩,⟨2153,by decide⟩,⟨2154,by decide⟩] | 2 => ![⟨1782,by decide⟩,⟨2155,by decide⟩,⟨2156,by decide⟩] | 3 => ![⟨2157,by decide⟩,⟨2158,by decide⟩,⟨2159,by decide⟩] | 4 => ![⟨2160,by decide⟩,⟨2161,by decide⟩,⟨2162,by decide⟩] | 5 => ![⟨2163,by decide⟩,⟨2164,by decide⟩,⟨1406,by decide⟩] | _ => ![⟨2165,by decide⟩,⟨1814,by decide⟩,⟨2166,by decide⟩]

def ntree8RLRLLLL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLRLLLLL i else ntree8RLRLLLLR (i - 7)

def ntree8RLRLLLRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2160,by decide⟩,⟨2167,by decide⟩,⟨2168,by decide⟩] | 1 => ![⟨2169,by decide⟩,⟨2170,by decide⟩,⟨1413,by decide⟩] | 2 => ![⟨2171,by decide⟩,⟨1781,by decide⟩,⟨2172,by decide⟩] | 3 => ![⟨2173,by decide⟩,⟨2174,by decide⟩,⟨1417,by decide⟩] | 4 => ![⟨2175,by decide⟩,⟨2176,by decide⟩,⟨1420,by decide⟩] | 5 => ![⟨2177,by decide⟩,⟨2178,by decide⟩,⟨2179,by decide⟩] | _ => ![⟨2163,by decide⟩,⟨2180,by decide⟩,⟨1426,by decide⟩]

def ntree8RLRLLLRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2181,by decide⟩,⟨1825,by decide⟩,⟨2182,by decide⟩] | 1 => ![⟨2177,by decide⟩,⟨2183,by decide⟩,⟨2184,by decide⟩] | 2 => ![⟨2169,by decide⟩,⟨2185,by decide⟩,⟨1433,by decide⟩] | 3 => ![⟨2186,by decide⟩,⟨1830,by decide⟩,⟨2187,by decide⟩] | 4 => ![⟨2173,by decide⟩,⟨2188,by decide⟩,⟨1437,by decide⟩] | 5 => ![⟨2175,by decide⟩,⟨2189,by decide⟩,⟨1439,by decide⟩] | _ => ![⟨2177,by decide⟩,⟨2161,by decide⟩,⟨2190,by decide⟩]

def ntree8RLRLLLR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLRLLLRL i else ntree8RLRLLLRR (i - 7)

def ntree8RLRLLL (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RLRLLLL i else ntree8RLRLLLR (i - 14)

def ntree8RLRLLRLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2191,by decide⟩,⟨2192,by decide⟩,⟨1446,by decide⟩] | 1 => ![⟨2193,by decide⟩,⟨1840,by decide⟩,⟨2194,by decide⟩] | 2 => ![⟨2177,by decide⟩,⟨2167,by decide⟩,⟨2195,by decide⟩] | 3 => ![⟨2196,by decide⟩,⟨2197,by decide⟩,⟨1452,by decide⟩] | 4 => ![⟨2198,by decide⟩,⟨1843,by decide⟩,⟨2199,by decide⟩] | 5 => ![⟨2200,by decide⟩,⟨2201,by decide⟩,⟨1456,by decide⟩] | _ => ![⟨2202,by decide⟩,⟨2203,by decide⟩,⟨1461,by decide⟩]

def ntree8RLRLLRLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2204,by decide⟩,⟨2205,by decide⟩,⟨1466,by decide⟩] | 1 => ![⟨2206,by decide⟩,⟨2207,by decide⟩,⟨2208,by decide⟩] | 2 => ![⟨2206,by decide⟩,⟨2209,by decide⟩,⟨2210,by decide⟩] | 3 => ![⟨2211,by decide⟩,⟨2212,by decide⟩,⟨2213,by decide⟩] | 4 => ![⟨2206,by decide⟩,⟨2161,by decide⟩,⟨2089,by decide⟩] | 5 => ![⟨2214,by decide⟩,⟨2164,by decide⟩,⟨2215,by decide⟩] | _ => ![⟨2202,by decide⟩,⟨2216,by decide⟩,⟨1482,by decide⟩]

def ntree8RLRLLRL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLRLLRLL i else ntree8RLRLLRLR (i - 7)

def ntree8RLRLLRRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2204,by decide⟩,⟨2217,by decide⟩,⟨1487,by decide⟩] | 1 => ![⟨2218,by decide⟩,⟨2219,by decide⟩,⟨2220,by decide⟩] | 2 => ![⟨2218,by decide⟩,⟨2221,by decide⟩,⟨2222,by decide⟩] | 3 => ![⟨2223,by decide⟩,⟨2224,by decide⟩,⟨2225,by decide⟩] | 4 => ![⟨2218,by decide⟩,⟨2178,by decide⟩,⟨2099,by decide⟩] | 5 => ![⟨2226,by decide⟩,⟨2180,by decide⟩,⟨2227,by decide⟩] | _ => ![⟨2228,by decide⟩,⟨2229,by decide⟩,⟨1503,by decide⟩]

def ntree8RLRLLRRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2230,by decide⟩,⟨2231,by decide⟩,⟨1508,by decide⟩] | 1 => ![⟨2206,by decide⟩,⟨2219,by decide⟩,⟨2232,by decide⟩] | 2 => ![⟨2206,by decide⟩,⟨2221,by decide⟩,⟨2233,by decide⟩] | 3 => ![⟨2211,by decide⟩,⟨2224,by decide⟩,⟨2234,by decide⟩] | 4 => ![⟨2235,by decide⟩,⟨2192,by decide⟩,⟨2236,by decide⟩] | 5 => ![⟨2237,by decide⟩,⟨2237,by decide⟩,⟨1116,by decide⟩] | _ => ![⟨1890,by decide⟩,⟨2238,by decide⟩,⟨2239,by decide⟩]

def ntree8RLRLLRR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLRLLRRL i else ntree8RLRLLRRR (i - 7)

def ntree8RLRLLR (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RLRLLRL i else ntree8RLRLLRR (i - 14)

def ntree8RLRLL (i : Nat) : Fin 3 → Fin 3321 := if i < 28 then ntree8RLRLLL i else ntree8RLRLLR (i - 28)

def ntree8RLRLRLLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2240,by decide⟩,⟨2237,by decide⟩,⟨1983,by decide⟩] | 1 => ![⟨1892,by decide⟩,⟨2241,by decide⟩,⟨1121,by decide⟩] | 2 => ![⟨1893,by decide⟩,⟨2242,by decide⟩,⟨2243,by decide⟩] | 3 => ![⟨2244,by decide⟩,⟨2245,by decide⟩,⟨1126,by decide⟩] | 4 => ![⟨2246,by decide⟩,⟨2247,by decide⟩,⟨1992,by decide⟩] | 5 => ![⟨1888,by decide⟩,⟨2248,by decide⟩,⟨2249,by decide⟩] | _ => ![⟨2237,by decide⟩,⟨2237,by decide⟩,⟨6,by decide⟩]

def ntree8RLRLRLLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1888,by decide⟩,⟨2250,by decide⟩,⟨1133,by decide⟩] | 1 => ![⟨1894,by decide⟩,⟨2251,by decide⟩,⟨2252,by decide⟩] | 2 => ![⟨2253,by decide⟩,⟨2254,by decide⟩,⟨1138,by decide⟩] | 3 => ![⟨2247,by decide⟩,⟨2247,by decide⟩,⟨1214,by decide⟩] | 4 => ![⟨1888,by decide⟩,⟨1888,by decide⟩,⟨1141,by decide⟩] | 5 => ![⟨2255,by decide⟩,⟨1888,by decide⟩,⟨2007,by decide⟩] | _ => ![⟨1892,by decide⟩,⟨2256,by decide⟩,⟨2257,by decide⟩]

def ntree8RLRLRLL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLRLRLLL i else ntree8RLRLRLLR (i - 7)

def ntree8RLRLRLRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1782,by decide⟩,⟨2258,by decide⟩,⟨1147,by decide⟩] | 1 => ![⟨2259,by decide⟩,⟨2260,by decide⟩,⟨2017,by decide⟩] | 2 => ![⟨2261,by decide⟩,⟨2261,by decide⟩,⟨2262,by decide⟩] | 3 => ![⟨2263,by decide⟩,⟨2209,by decide⟩,⟨2264,by decide⟩] | 4 => ![⟨2265,by decide⟩,⟨2253,by decide⟩,⟨2266,by decide⟩] | 5 => ![⟨2267,by decide⟩,⟨2167,by decide⟩,⟨2268,by decide⟩] | _ => ![⟨2269,by decide⟩,⟨2170,by decide⟩,⟨2270,by decide⟩]

def ntree8RLRLRLRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2261,by decide⟩,⟨2271,by decide⟩,⟨1570,by decide⟩] | 1 => ![⟨2272,by decide⟩,⟨2221,by decide⟩,⟨2273,by decide⟩] | 2 => ![⟨2253,by decide⟩,⟨2274,by decide⟩,⟨362,by decide⟩] | 3 => ![⟨2275,by decide⟩,⟨2183,by decide⟩,⟨2276,by decide⟩] | 4 => ![⟨2277,by decide⟩,⟨2185,by decide⟩,⟨2278,by decide⟩] | 5 => ![⟨2261,by decide⟩,⟨2279,by decide⟩,⟨1582,by decide⟩] | _ => ![⟨2247,by decide⟩,⟨2280,by decide⟩,⟨1585,by decide⟩]

def ntree8RLRLRLR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLRLRLRL i else ntree8RLRLRLRR (i - 7)

def ntree8RLRLRL (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RLRLRLL i else ntree8RLRLRLR (i - 14)

def ntree8RLRLRRLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2281,by decide⟩,⟨2281,by decide⟩,⟨2282,by decide⟩] | 1 => ![⟨2283,by decide⟩,⟨1843,by decide⟩,⟨2284,by decide⟩] | 2 => ![⟨2285,by decide⟩,⟨2197,by decide⟩,⟨2286,by decide⟩] | 3 => ![⟨2281,by decide⟩,⟨2287,by decide⟩,⟨1598,by decide⟩] | 4 => ![⟨2260,by decide⟩,⟨2288,by decide⟩,⟨1601,by decide⟩] | 5 => ![⟨2289,by decide⟩,⟨2289,by decide⟩,⟨1603,by decide⟩] | _ => ![⟨2290,by decide⟩,⟨2291,by decide⟩,⟨1604,by decide⟩]

def ntree8RLRLRRLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2292,by decide⟩,⟨2290,by decide⟩,⟨2082,by decide⟩] | 1 => ![⟨2292,by decide⟩,⟨2291,by decide⟩,⟨2293,by decide⟩] | 2 => ![⟨2294,by decide⟩,⟨2261,by decide⟩,⟨2086,by decide⟩] | 3 => ![⟨2244,by decide⟩,⟨2253,by decide⟩,⟨863,by decide⟩] | 4 => ![⟨2290,by decide⟩,⟨2295,by decide⟩,⟨1615,by decide⟩] | 5 => ![⟨2237,by decide⟩,⟨2296,by decide⟩,⟨401,by decide⟩] | _ => ![⟨2297,by decide⟩,⟨2290,by decide⟩,⟨2092,by decide⟩]

def ntree8RLRLRRL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLRLRRLL i else ntree8RLRLRRLR (i - 7)

def ntree8RLRLRRRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2297,by decide⟩,⟨2295,by decide⟩,⟨2298,by decide⟩] | 1 => ![⟨2299,by decide⟩,⟨2261,by decide⟩,⟨2096,by decide⟩] | 2 => ![⟨2300,by decide⟩,⟨2300,by decide⟩,⟨1622,by decide⟩] | 3 => ![⟨2292,by decide⟩,⟨2295,by decide⟩,⟨2301,by decide⟩] | 4 => ![⟨2302,by decide⟩,⟨2281,by decide⟩,⟨2104,by decide⟩] | 5 => ![⟨2303,by decide⟩,⟨2304,by decide⟩,⟨2305,by decide⟩] | _ => ![⟨2306,by decide⟩,⟨2307,by decide⟩,⟨2308,by decide⟩]

def ntree8RLRLRRRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2309,by decide⟩,⟨2310,by decide⟩,⟨2305,by decide⟩] | 1 => ![⟨2311,by decide⟩,⟨2312,by decide⟩,⟨2313,by decide⟩] | 2 => ![⟨2314,by decide⟩,⟨2314,by decide⟩,⟨2315,by decide⟩] | 3 => ![⟨2316,by decide⟩,⟨2317,by decide⟩,⟨2318,by decide⟩] | 4 => ![⟨2319,by decide⟩,⟨2320,by decide⟩,⟨2321,by decide⟩] | 5 => ![⟨2322,by decide⟩,⟨2323,by decide⟩,⟨2324,by decide⟩] | 6 => ![⟨2325,by decide⟩,⟨2326,by decide⟩,⟨2327,by decide⟩] | _ => ![⟨2328,by decide⟩,⟨2329,by decide⟩,⟨2330,by decide⟩]

def ntree8RLRLRRR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLRLRRRL i else ntree8RLRLRRRR (i - 7)

def ntree8RLRLRR (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RLRLRRL i else ntree8RLRLRRR (i - 14)

def ntree8RLRLR (i : Nat) : Fin 3 → Fin 3321 := if i < 28 then ntree8RLRLRL i else ntree8RLRLRR (i - 28)

def ntree8RLRL (i : Nat) : Fin 3 → Fin 3321 := if i < 56 then ntree8RLRLL i else ntree8RLRLR (i - 56)

def ntree8RLRRLLLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2331,by decide⟩,⟨2332,by decide⟩,⟨2333,by decide⟩] | 1 => ![⟨2334,by decide⟩,⟨2335,by decide⟩,⟨2330,by decide⟩] | 2 => ![⟨2336,by decide⟩,⟨2337,by decide⟩,⟨2338,by decide⟩] | 3 => ![⟨2339,by decide⟩,⟨2340,by decide⟩,⟨2341,by decide⟩] | 4 => ![⟨2342,by decide⟩,⟨2343,by decide⟩,⟨2344,by decide⟩] | 5 => ![⟨2345,by decide⟩,⟨2346,by decide⟩,⟨2347,by decide⟩] | _ => ![⟨2348,by decide⟩,⟨1214,by decide⟩,⟨2349,by decide⟩]

def ntree8RLRRLLLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2350,by decide⟩,⟨2351,by decide⟩,⟨2352,by decide⟩] | 1 => ![⟨2353,by decide⟩,⟨2354,by decide⟩,⟨2352,by decide⟩] | 2 => ![⟨2355,by decide⟩,⟨2355,by decide⟩,⟨2356,by decide⟩] | 3 => ![⟨2357,by decide⟩,⟨2358,by decide⟩,⟨2359,by decide⟩] | 4 => ![⟨2360,by decide⟩,⟨2361,by decide⟩,⟨2362,by decide⟩] | 5 => ![⟨2363,by decide⟩,⟨2364,by decide⟩,⟨2365,by decide⟩] | _ => ![⟨2366,by decide⟩,⟨2367,by decide⟩,⟨2368,by decide⟩]

def ntree8RLRRLLL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLRRLLLL i else ntree8RLRRLLLR (i - 7)

def ntree8RLRRLLRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2369,by decide⟩,⟨56,by decide⟩,⟨2370,by decide⟩] | 1 => ![⟨2371,by decide⟩,⟨59,by decide⟩,⟨2372,by decide⟩] | 2 => ![⟨2373,by decide⟩,⟨62,by decide⟩,⟨2321,by decide⟩] | 3 => ![⟨2374,by decide⟩,⟨63,by decide⟩,⟨2375,by decide⟩] | 4 => ![⟨2376,by decide⟩,⟨2376,by decide⟩,⟨2377,by decide⟩] | 5 => ![⟨2378,by decide⟩,⟨2379,by decide⟩,⟨2380,by decide⟩] | _ => ![⟨2381,by decide⟩,⟨57,by decide⟩,⟨2370,by decide⟩]

def ntree8RLRRLLRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2382,by decide⟩,⟨2383,by decide⟩,⟨2384,by decide⟩] | 1 => ![⟨2385,by decide⟩,⟨55,by decide⟩,⟨2386,by decide⟩] | 2 => ![⟨2387,by decide⟩,⟨58,by decide⟩,⟨2388,by decide⟩] | 3 => ![⟨2389,by decide⟩,⟨61,by decide⟩,⟨2344,by decide⟩] | 4 => ![⟨2390,by decide⟩,⟨58,by decide⟩,⟨2391,by decide⟩] | 5 => ![⟨2392,by decide⟩,⟨2393,by decide⟩,⟨2394,by decide⟩] | _ => ![⟨2395,by decide⟩,⟨70,by decide⟩,⟨2386,by decide⟩]

def ntree8RLRRLLR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLRRLLRL i else ntree8RLRRLLRR (i - 7)

def ntree8RLRRLL (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RLRRLLL i else ntree8RLRRLLR (i - 14)

def ntree8RLRRLRLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2396,by decide⟩,⟨2397,by decide⟩,⟨2398,by decide⟩] | 1 => ![⟨2399,by decide⟩,⟨59,by decide⟩,⟨2400,by decide⟩] | 2 => ![⟨2401,by decide⟩,⟨89,by decide⟩,⟨2362,by decide⟩] | 3 => ![⟨58,by decide⟩,⟨58,by decide⟩,⟨2402,by decide⟩] | 4 => ![⟨2403,by decide⟩,⟨2404,by decide⟩,⟨2405,by decide⟩] | 5 => ![⟨2406,by decide⟩,⟨60,by decide⟩,⟨2400,by decide⟩] | _ => ![⟨2407,by decide⟩,⟨60,by decide⟩,⟨2408,by decide⟩]

def ntree8RLRRLRLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2409,by decide⟩,⟨2410,by decide⟩,⟨2411,by decide⟩] | 1 => ![⟨2412,by decide⟩,⟨2413,by decide⟩,⟨2414,by decide⟩] | 2 => ![⟨2415,by decide⟩,⟨2416,by decide⟩,⟨2417,by decide⟩] | 3 => ![⟨2418,by decide⟩,⟨2418,by decide⟩,⟨2419,by decide⟩] | 4 => ![⟨2420,by decide⟩,⟨2421,by decide⟩,⟨2313,by decide⟩] | 5 => ![⟨2422,by decide⟩,⟨107,by decide⟩,⟨2372,by decide⟩] | _ => ![⟨2423,by decide⟩,⟨109,by decide⟩,⟨2321,by decide⟩]

def ntree8RLRRLRL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLRRLRLL i else ntree8RLRRLRLR (i - 7)

def ntree8RLRRLRRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2424,by decide⟩,⟨2425,by decide⟩,⟨2426,by decide⟩] | 1 => ![⟨2427,by decide⟩,⟨2428,by decide⟩,⟨2429,by decide⟩] | 2 => ![⟨2430,by decide⟩,⟨2431,by decide⟩,⟨2432,by decide⟩] | 3 => ![⟨2433,by decide⟩,⟨2434,by decide⟩,⟨2338,by decide⟩] | 4 => ![⟨2435,by decide⟩,⟨116,by decide⟩,⟨2388,by decide⟩] | 5 => ![⟨2436,by decide⟩,⟨118,by decide⟩,⟨2344,by decide⟩] | _ => ![⟨2437,by decide⟩,⟨2438,by decide⟩,⟨2439,by decide⟩]

def ntree8RLRRLRRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2440,by decide⟩,⟨2440,by decide⟩,⟨2419,by decide⟩] | 1 => ![⟨2441,by decide⟩,⟨2442,by decide⟩,⟨2338,by decide⟩] | 2 => ![⟨2443,by decide⟩,⟨124,by decide⟩,⟨2372,by decide⟩] | 3 => ![⟨2444,by decide⟩,⟨126,by decide⟩,⟨2362,by decide⟩] | 4 => ![⟨2445,by decide⟩,⟨2446,by decide⟩,⟨2447,by decide⟩] | 5 => ![⟨1342,by decide⟩,⟨131,by decide⟩,⟨2448,by decide⟩] | 6 => ![⟨2449,by decide⟩,⟨2450,by decide⟩,⟨2447,by decide⟩] | _ => ![⟨2451,by decide⟩,⟨2452,by decide⟩,⟨2453,by decide⟩]

def ntree8RLRRLRR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLRRLRRL i else ntree8RLRRLRRR (i - 7)

def ntree8RLRRLR (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RLRRLRL i else ntree8RLRRLRR (i - 14)

def ntree8RLRRL (i : Nat) : Fin 3 → Fin 3321 := if i < 28 then ntree8RLRRLL i else ntree8RLRRLR (i - 28)

def ntree8RLRRRLLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1350,by decide⟩,⟨1369,by decide⟩,⟨2454,by decide⟩] | 1 => ![⟨2455,by decide⟩,⟨2456,by decide⟩,⟨2457,by decide⟩] | 2 => ![⟨2458,by decide⟩,⟨2459,by decide⟩,⟨2460,by decide⟩] | 3 => ![⟨1353,by decide⟩,⟨2461,by decide⟩,⟨2461,by decide⟩] | 4 => ![⟨2455,by decide⟩,⟨2462,by decide⟩,⟨2463,by decide⟩] | 5 => ![⟨2464,by decide⟩,⟨2465,by decide⟩,⟨2466,by decide⟩] | _ => ![⟨2467,by decide⟩,⟨153,by decide⟩,⟨2468,by decide⟩]

def ntree8RLRRRLLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2469,by decide⟩,⟨2470,by decide⟩,⟨2466,by decide⟩] | 1 => ![⟨2471,by decide⟩,⟨2472,by decide⟩,⟨2473,by decide⟩] | 2 => ![⟨1369,by decide⟩,⟨2474,by decide⟩,⟨2475,by decide⟩] | 3 => ![⟨2476,by decide⟩,⟨2477,by decide⟩,⟨2478,by decide⟩] | 4 => ![⟨2479,by decide⟩,⟨2480,by decide⟩,⟨2481,by decide⟩] | 5 => ![⟨2482,by decide⟩,⟨2475,by decide⟩,⟨2475,by decide⟩] | _ => ![⟨2476,by decide⟩,⟨2483,by decide⟩,⟨2484,by decide⟩]

def ntree8RLRRRLL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLRRRLLL i else ntree8RLRRRLLR (i - 7)

def ntree8RLRRRLRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2485,by decide⟩,⟨2486,by decide⟩,⟨2487,by decide⟩] | 1 => ![⟨2488,by decide⟩,⟨2489,by decide⟩,⟨2487,by decide⟩] | 2 => ![⟨2490,by decide⟩,⟨2491,by decide⟩,⟨2492,by decide⟩] | 3 => ![⟨1347,by decide⟩,⟨153,by decide⟩,⟨2493,by decide⟩] | 4 => ![⟨2494,by decide⟩,⟨2495,by decide⟩,⟨2496,by decide⟩] | 5 => ![⟨2497,by decide⟩,⟨2498,by decide⟩,⟨2499,by decide⟩] | _ => ![⟨2500,by decide⟩,⟨175,by decide⟩,⟨175,by decide⟩]

def ntree8RLRRRLRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2494,by decide⟩,⟨2501,by decide⟩,⟨2502,by decide⟩] | 1 => ![⟨2374,by decide⟩,⟨59,by decide⟩,⟨2503,by decide⟩] | 2 => ![⟨2504,by decide⟩,⟨89,by decide⟩,⟨2505,by decide⟩] | 3 => ![⟨2374,by decide⟩,⟨58,by decide⟩,⟨2506,by decide⟩] | 4 => ![⟨2376,by decide⟩,⟨2376,by decide⟩,⟨2397,by decide⟩] | 5 => ![⟨2378,by decide⟩,⟨2393,by decide⟩,⟨2507,by decide⟩] | _ => ![⟨2508,by decide⟩,⟨60,by decide⟩,⟨2509,by decide⟩]

def ntree8RLRRRLR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLRRRLRL i else ntree8RLRRRLRR (i - 7)

def ntree8RLRRRL (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RLRRRLL i else ntree8RLRRRLR (i - 14)

def ntree8RLRRRRLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2397,by decide⟩,⟨2383,by decide⟩,⟨2383,by decide⟩] | 1 => ![⟨2510,by decide⟩,⟨2461,by decide⟩,⟨2511,by decide⟩] | 2 => ![⟨2390,by decide⟩,⟨58,by decide⟩,⟨2512,by decide⟩] | 3 => ![⟨2513,by decide⟩,⟨212,by decide⟩,⟨2514,by decide⟩] | 4 => ![⟨2390,by decide⟩,⟨2515,by decide⟩,⟨2516,by decide⟩] | 5 => ![⟨2376,by decide⟩,⟨2517,by decide⟩,⟨2518,by decide⟩] | _ => ![⟨2392,by decide⟩,⟨2519,by decide⟩,⟨2520,by decide⟩]

def ntree8RLRRRRLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2521,by decide⟩,⟨2522,by decide⟩,⟨2523,by decide⟩] | 1 => ![⟨2397,by decide⟩,⟨2518,by decide⟩,⟨2518,by decide⟩] | 2 => ![⟨2524,by decide⟩,⟨1581,by decide⟩,⟨2525,by decide⟩] | 3 => ![⟨2390,by decide⟩,⟨59,by decide⟩,⟨2526,by decide⟩] | 4 => ![⟨2527,by decide⟩,⟨231,by decide⟩,⟨2528,by decide⟩] | 5 => ![⟨2390,by decide⟩,⟨58,by decide⟩,⟨2529,by decide⟩] | _ => ![⟨2403,by decide⟩,⟨212,by decide⟩,⟨2530,by decide⟩]

def ntree8RLRRRRL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLRRRRLL i else ntree8RLRRRRLR (i - 7)

def ntree8RLRRRRRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2521,by decide⟩,⟨60,by decide⟩,⟨2531,by decide⟩] | 1 => ![⟨2532,by decide⟩,⟨280,by decide⟩,⟨2533,by decide⟩] | 2 => ![⟨2534,by decide⟩,⟨2535,by decide⟩,⟨2536,by decide⟩] | 3 => ![⟨2537,by decide⟩,⟨60,by decide⟩,⟨2538,by decide⟩] | 4 => ![⟨2539,by decide⟩,⟨2540,by decide⟩,⟨2541,by decide⟩] | 5 => ![⟨2542,by decide⟩,⟨2543,by decide⟩,⟨2544,by decide⟩] | _ => ![⟨2545,by decide⟩,⟨2546,by decide⟩,⟨2537,by decide⟩]

def ntree8RLRRRRRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2547,by decide⟩,⟨2548,by decide⟩,⟨2549,by decide⟩] | 1 => ![⟨2542,by decide⟩,⟨259,by decide⟩,⟨2503,by decide⟩] | 2 => ![⟨2550,by decide⟩,⟨60,by decide⟩,⟨60,by decide⟩] | 3 => ![⟨2551,by decide⟩,⟨262,by decide⟩,⟨2505,by decide⟩] | 4 => ![⟨2552,by decide⟩,⟨2553,by decide⟩,⟨2554,by decide⟩] | 5 => ![⟨2555,by decide⟩,⟨211,by decide⟩,⟨2556,by decide⟩] | 6 => ![⟨2557,by decide⟩,⟨2558,by decide⟩,⟨2559,by decide⟩] | _ => ![⟨2560,by decide⟩,⟨2561,by decide⟩,⟨2562,by decide⟩]

def ntree8RLRRRRR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RLRRRRRL i else ntree8RLRRRRRR (i - 7)

def ntree8RLRRRR (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RLRRRRL i else ntree8RLRRRRR (i - 14)

def ntree8RLRRR (i : Nat) : Fin 3 → Fin 3321 := if i < 28 then ntree8RLRRRL i else ntree8RLRRRR (i - 28)

def ntree8RLRR (i : Nat) : Fin 3 → Fin 3321 := if i < 57 then ntree8RLRRL i else ntree8RLRRR (i - 57)

def ntree8RLR (i : Nat) : Fin 3 → Fin 3321 := if i < 113 then ntree8RLRL i else ntree8RLRR (i - 113)

def ntree8RL (i : Nat) : Fin 3 → Fin 3321 := if i < 226 then ntree8RLL i else ntree8RLR (i - 226)

def ntree8RRLLLLLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2546,by decide⟩,⟨2563,by decide⟩,⟨211,by decide⟩] | 1 => ![⟨2564,by decide⟩,⟨2565,by decide⟩,⟨2566,by decide⟩] | 2 => ![⟨2560,by decide⟩,⟨274,by decide⟩,⟨2512,by decide⟩] | 3 => ![⟨2567,by decide⟩,⟨211,by decide⟩,⟨211,by decide⟩] | 4 => ![⟨2568,by decide⟩,⟨277,by decide⟩,⟨2514,by decide⟩] | 5 => ![⟨2569,by decide⟩,⟨2570,by decide⟩,⟨2571,by decide⟩] | _ => ![⟨2572,by decide⟩,⟨2573,by decide⟩,⟨2574,by decide⟩]

def ntree8RRLLLLLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2575,by decide⟩,⟨2576,by decide⟩,⟨2562,by decide⟩] | 1 => ![⟨2550,by decide⟩,⟨211,by decide⟩,⟨211,by decide⟩] | 2 => ![⟨2577,by decide⟩,⟨2578,by decide⟩,⟨2566,by decide⟩] | 3 => ![⟨2575,by decide⟩,⟨287,by decide⟩,⟨2526,by decide⟩] | 4 => ![⟨2579,by decide⟩,⟨229,by decide⟩,⟨229,by decide⟩] | 5 => ![⟨2580,by decide⟩,⟨290,by decide⟩,⟨2528,by decide⟩] | _ => ![⟨2309,by decide⟩,⟨2581,by decide⟩,⟨2309,by decide⟩]

def ntree8RRLLLLL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRLLLLLL i else ntree8RRLLLLLR (i - 7)

def ntree8RRLLLLRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2582,by decide⟩,⟨2583,by decide⟩,⟨2584,by decide⟩] | 1 => ![⟨2585,by decide⟩,⟨2586,by decide⟩,⟨2309,by decide⟩] | 2 => ![⟨2587,by decide⟩,⟨2588,by decide⟩,⟨2589,by decide⟩] | 3 => ![⟨2590,by decide⟩,⟨2591,by decide⟩,⟨2591,by decide⟩] | 4 => ![⟨2592,by decide⟩,⟨2593,by decide⟩,⟨2316,by decide⟩] | 5 => ![⟨2594,by decide⟩,⟨2595,by decide⟩,⟨2596,by decide⟩] | _ => ![⟨2597,by decide⟩,⟨2598,by decide⟩,⟨2599,by decide⟩]

def ntree8RRLLLLRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2600,by decide⟩,⟨2601,by decide⟩,⟨2325,by decide⟩] | 1 => ![⟨2334,by decide⟩,⟨2602,by decide⟩,⟨2334,by decide⟩] | 2 => ![⟨2603,by decide⟩,⟨2604,by decide⟩,⟨2605,by decide⟩] | 3 => ![⟨2606,by decide⟩,⟨2586,by decide⟩,⟨2334,by decide⟩] | 4 => ![⟨2607,by decide⟩,⟨2608,by decide⟩,⟨2609,by decide⟩] | 5 => ![⟨2610,by decide⟩,⟨2611,by decide⟩,⟨2611,by decide⟩] | _ => ![⟨2612,by decide⟩,⟨2593,by decide⟩,⟨2339,by decide⟩]

def ntree8RRLLLLR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRLLLLRL i else ntree8RRLLLLRR (i - 7)

def ntree8RRLLLL (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RRLLLLL i else ntree8RRLLLLR (i - 14)

def ntree8RRLLLRLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2613,by decide⟩,⟨2614,by decide⟩,⟨2615,by decide⟩] | 1 => ![⟨2616,by decide⟩,⟨2617,by decide⟩,⟨2618,by decide⟩] | 2 => ![⟨2619,by decide⟩,⟨2601,by decide⟩,⟨2348,by decide⟩] | 3 => ![⟨2353,by decide⟩,⟨2620,by decide⟩,⟨2353,by decide⟩] | 4 => ![⟨2621,by decide⟩,⟨2622,by decide⟩,⟨2623,by decide⟩] | 5 => ![⟨2624,by decide⟩,⟨2625,by decide⟩,⟨2353,by decide⟩] | _ => ![⟨2626,by decide⟩,⟨2627,by decide⟩,⟨2628,by decide⟩]

def ntree8RRLLLRLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2629,by decide⟩,⟨2630,by decide⟩,⟨2630,by decide⟩] | 1 => ![⟨2631,by decide⟩,⟨2632,by decide⟩,⟨2357,by decide⟩] | 2 => ![⟨2633,by decide⟩,⟨2634,by decide⟩,⟨2635,by decide⟩] | 3 => ![⟨2636,by decide⟩,⟨2637,by decide⟩,⟨2638,by decide⟩] | 4 => ![⟨2639,by decide⟩,⟨2640,by decide⟩,⟨2366,by decide⟩] | 5 => ![⟨2381,by decide⟩,⟨344,by decide⟩,⟨2381,by decide⟩] | _ => ![⟨2641,by decide⟩,⟨346,by decide⟩,⟨2642,by decide⟩]

def ntree8RRLLLRL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRLLLRLL i else ntree8RRLLLRLR (i - 7)

def ntree8RRLLLRRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2643,by decide⟩,⟨349,by decide⟩,⟨2644,by decide⟩] | 1 => ![⟨2645,by decide⟩,⟨2646,by decide⟩,⟨2506,by decide⟩] | 2 => ![⟨2647,by decide⟩,⟨2397,by decide⟩,⟨2397,by decide⟩] | 3 => ![⟨2648,by decide⟩,⟨2649,by decide⟩,⟨2507,by decide⟩] | 4 => ![⟨2381,by decide⟩,⟨70,by decide⟩,⟨2650,by decide⟩] | 5 => ![⟨2382,by decide⟩,⟨2397,by decide⟩,⟨2651,by decide⟩] | _ => ![⟨2325,by decide⟩,⟨1214,by decide⟩,⟨2652,by decide⟩]

def ntree8RRLLLRRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2395,by decide⟩,⟨70,by decide⟩,⟨2395,by decide⟩] | 1 => ![⟨2653,by decide⟩,⟨211,by decide⟩,⟨2654,by decide⟩] | 2 => ![⟨2655,by decide⟩,⟨362,by decide⟩,⟨2656,by decide⟩] | 3 => ![⟨2657,by decide⟩,⟨2522,by decide⟩,⟨2516,by decide⟩] | 4 => ![⟨2658,by decide⟩,⟨2518,by decide⟩,⟨2518,by decide⟩] | 5 => ![⟨2659,by decide⟩,⟨1581,by decide⟩,⟨2520,by decide⟩] | _ => ![⟨2395,by decide⟩,⟨2660,by decide⟩,⟨2661,by decide⟩]

def ntree8RRLLLRR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRLLLRRL i else ntree8RRLLLRRR (i - 7)

def ntree8RRLLLR (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RRLLLRL i else ntree8RRLLLRR (i - 14)

def ntree8RRLLL (i : Nat) : Fin 3 → Fin 3321 := if i < 28 then ntree8RRLLLL i else ntree8RRLLLR (i - 28)

def ntree8RRLLRLLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2396,by decide⟩,⟨2518,by decide⟩,⟨2662,by decide⟩] | 1 => ![⟨2348,by decide⟩,⟨1585,by decide⟩,⟨2663,by decide⟩] | 2 => ![⟨2406,by decide⟩,⟨346,by decide⟩,⟨2406,by decide⟩] | 3 => ![⟨2664,by decide⟩,⟨375,by decide⟩,⟨2665,by decide⟩] | 4 => ![⟨2666,by decide⟩,⟨376,by decide⟩,⟨2667,by decide⟩] | 5 => ![⟨2668,by decide⟩,⟨2669,by decide⟩,⟨2529,by decide⟩] | _ => ![⟨2670,by decide⟩,⟨211,by decide⟩,⟨211,by decide⟩]

def ntree8RRLLRLLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2671,by decide⟩,⟨2672,by decide⟩,⟨2530,by decide⟩] | 1 => ![⟨2406,by decide⟩,⟨2673,by decide⟩,⟨2674,by decide⟩] | 2 => ![⟨2407,by decide⟩,⟨211,by decide⟩,⟨2675,by decide⟩] | 3 => ![⟨2366,by decide⟩,⟨1601,by decide⟩,⟨2676,by decide⟩] | 4 => ![⟨2409,by decide⟩,⟨2677,by decide⟩,⟨2409,by decide⟩] | 5 => ![⟨2412,by decide⟩,⟨2678,by decide⟩,⟨2679,by decide⟩] | _ => ![⟨2309,by decide⟩,⟨2680,by decide⟩,⟨2681,by decide⟩]

def ntree8RRLLRLL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRLLRLLL i else ntree8RRLLRLLR (i - 7)

def ntree8RRLLRLRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2682,by decide⟩,⟨2683,by decide⟩,⟨2415,by decide⟩] | 1 => ![⟨2684,by decide⟩,⟨2678,by decide⟩,⟨2678,by decide⟩] | 2 => ![⟨2587,by decide⟩,⟨2685,by decide⟩,⟨2686,by decide⟩] | 3 => ![⟨2687,by decide⟩,⟨395,by decide⟩,⟨2381,by decide⟩] | 4 => ![⟨2688,by decide⟩,⟨397,by decide⟩,⟨2642,by decide⟩] | 5 => ![⟨2594,by decide⟩,⟨398,by decide⟩,⟨2644,by decide⟩] | _ => ![⟨2424,by decide⟩,⟨2677,by decide⟩,⟨2424,by decide⟩]

def ntree8RRLLRLRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2427,by decide⟩,⟨2689,by decide⟩,⟨2690,by decide⟩] | 1 => ![⟨2334,by decide⟩,⟨2691,by decide⟩,⟨2692,by decide⟩] | 2 => ![⟨2693,by decide⟩,⟨2683,by decide⟩,⟨2430,by decide⟩] | 3 => ![⟨2694,by decide⟩,⟨2689,by decide⟩,⟨2689,by decide⟩] | 4 => ![⟨2607,by decide⟩,⟨2695,by decide⟩,⟨2696,by decide⟩] | 5 => ![⟨2697,by decide⟩,⟨395,by decide⟩,⟨2395,by decide⟩] | _ => ![⟨2698,by decide⟩,⟨409,by decide⟩,⟨2654,by decide⟩]

def ntree8RRLLRLR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRLLRLRL i else ntree8RRLLRLRR (i - 7)

def ntree8RRLLRL (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RRLLRLL i else ntree8RRLLRLR (i - 14)

def ntree8RRLLRRLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2613,by decide⟩,⟨410,by decide⟩,⟨2656,by decide⟩] | 1 => ![⟨2437,by decide⟩,⟨2699,by decide⟩,⟨2437,by decide⟩] | 2 => ![⟨2412,by decide⟩,⟨2689,by decide⟩,⟨2700,by decide⟩] | 3 => ![⟨2353,by decide⟩,⟨2701,by decide⟩,⟨2702,by decide⟩] | 4 => ![⟨2703,by decide⟩,⟨2704,by decide⟩,⟨2430,by decide⟩] | 5 => ![⟨2684,by decide⟩,⟨2689,by decide⟩,⟨2689,by decide⟩] | _ => ![⟨2626,by decide⟩,⟨2705,by decide⟩,⟨2696,by decide⟩]

def ntree8RRLLRRLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2706,by decide⟩,⟨416,by decide⟩,⟨2406,by decide⟩] | 1 => ![⟨2688,by decide⟩,⟨409,by decide⟩,⟨2665,by decide⟩] | 2 => ![⟨2633,by decide⟩,⟨417,by decide⟩,⟨2667,by decide⟩] | 3 => ![⟨2311,by decide⟩,⟨2307,by decide⟩,⟨2707,by decide⟩] | 4 => ![⟨2708,by decide⟩,⟨2307,by decide⟩,⟨2709,by decide⟩] | 5 => ![⟨2710,by decide⟩,⟨2711,by decide⟩,⟨2712,by decide⟩] | _ => ![⟨2713,by decide⟩,⟨2714,by decide⟩,⟨2715,by decide⟩]

def ntree8RRLLRRL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRLLRRLL i else ntree8RRLLRRLR (i - 7)

def ntree8RRLLRRRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2716,by decide⟩,⟨2314,by decide⟩,⟨2717,by decide⟩] | 1 => ![⟨2718,by decide⟩,⟨2719,by decide⟩,⟨2718,by decide⟩] | 2 => ![⟨2720,by decide⟩,⟨2721,by decide⟩,⟨2722,by decide⟩] | 3 => ![⟨2723,by decide⟩,⟨2323,by decide⟩,⟨2724,by decide⟩] | 4 => ![⟨2725,by decide⟩,⟨2726,by decide⟩,⟨2727,by decide⟩] | 5 => ![⟨2336,by decide⟩,⟨2332,by decide⟩,⟨2728,by decide⟩] | _ => ![⟨2729,by decide⟩,⟨2332,by decide⟩,⟨2730,by decide⟩]

def ntree8RRLLRRRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2731,by decide⟩,⟨2732,by decide⟩,⟨2733,by decide⟩] | 1 => ![⟨2734,by decide⟩,⟨2714,by decide⟩,⟨2735,by decide⟩] | 2 => ![⟨2736,by decide⟩,⟨2314,by decide⟩,⟨2737,by decide⟩] | 3 => ![⟨2738,by decide⟩,⟨2719,by decide⟩,⟨2738,by decide⟩] | 4 => ![⟨2739,by decide⟩,⟨2740,by decide⟩,⟨2741,by decide⟩] | 5 => ![⟨2742,by decide⟩,⟨2346,by decide⟩,⟨2743,by decide⟩] | 6 => ![⟨2744,by decide⟩,⟨2745,by decide⟩,⟨2746,by decide⟩] | _ => ![⟨2336,by decide⟩,⟨2307,by decide⟩,⟨2747,by decide⟩]

def ntree8RRLLRRR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRLLRRRL i else ntree8RRLLRRRR (i - 7)

def ntree8RRLLRR (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RRLLRRL i else ntree8RRLLRRR (i - 14)

def ntree8RRLLR (i : Nat) : Fin 3 → Fin 3321 := if i < 28 then ntree8RRLLRL i else ntree8RRLLRR (i - 28)

def ntree8RRLL (i : Nat) : Fin 3 → Fin 3321 := if i < 56 then ntree8RRLLL i else ntree8RRLLR (i - 56)

def ntree8RRLRLLLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2729,by decide⟩,⟨2307,by decide⟩,⟨2748,by decide⟩] | 1 => ![⟨2731,by decide⟩,⟨2711,by decide⟩,⟨2749,by decide⟩] | 2 => ![⟨2750,by decide⟩,⟨2751,by decide⟩,⟨2752,by decide⟩] | 3 => ![⟨2753,by decide⟩,⟨2355,by decide⟩,⟨2754,by decide⟩] | 4 => ![⟨2755,by decide⟩,⟨2756,by decide⟩,⟨2755,by decide⟩] | 5 => ![⟨2757,by decide⟩,⟨2758,by decide⟩,⟨2759,by decide⟩] | _ => ![⟨2760,by decide⟩,⟨2364,by decide⟩,⟨430,by decide⟩]

def ntree8RRLRLLLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2761,by decide⟩,⟨2762,by decide⟩,⟨2763,by decide⟩] | 1 => ![⟨2764,by decide⟩,⟨469,by decide⟩,⟨2765,by decide⟩] | 2 => ![⟨2766,by decide⟩,⟨131,by decide⟩,⟨2767,by decide⟩] | 3 => ![⟨2768,by decide⟩,⟨2769,by decide⟩,⟨2770,by decide⟩] | 4 => ![⟨2771,by decide⟩,⟨478,by decide⟩,⟨2772,by decide⟩] | 5 => ![⟨2773,by decide⟩,⟨1369,by decide⟩,⟨2774,by decide⟩] | _ => ![⟨2775,by decide⟩,⟨2649,by decide⟩,⟨2775,by decide⟩]

def ntree8RRLRLLL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRLRLLLL i else ntree8RRLRLLLR (i - 7)

def ntree8RRLRLLRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2776,by decide⟩,⟨470,by decide⟩,⟨2765,by decide⟩] | 1 => ![⟨2777,by decide⟩,⟨2461,by decide⟩,⟨2778,by decide⟩] | 2 => ![⟨2779,by decide⟩,⟨2461,by decide⟩,⟨2463,by decide⟩] | 3 => ![⟨2780,by decide⟩,⟨468,by decide⟩,⟨2781,by decide⟩] | 4 => ![⟨2782,by decide⟩,⟨1711,by decide⟩,⟨2783,by decide⟩] | 5 => ![⟨2784,by decide⟩,⟨2785,by decide⟩,⟨2786,by decide⟩] | _ => ![⟨2787,by decide⟩,⟨1691,by decide⟩,⟨2788,by decide⟩]

def ntree8RRLRLLRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2789,by decide⟩,⟨1693,by decide⟩,⟨2790,by decide⟩] | 1 => ![⟨2791,by decide⟩,⟨1695,by decide⟩,⟨2791,by decide⟩] | 2 => ![⟨2792,by decide⟩,⟨2793,by decide⟩,⟨2781,by decide⟩] | 3 => ![⟨2794,by decide⟩,⟨1695,by decide⟩,⟨2795,by decide⟩] | 4 => ![⟨2796,by decide⟩,⟨1695,by decide⟩,⟨2484,by decide⟩] | 5 => ![⟨2797,by decide⟩,⟨131,by decide⟩,⟨2798,by decide⟩] | _ => ![⟨2799,by decide⟩,⟨2800,by decide⟩,⟨2801,by decide⟩]

def ntree8RRLRLLR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRLRLLRL i else ntree8RRLRLLRR (i - 7)

def ntree8RRLRLL (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RRLRLLL i else ntree8RRLRLLR (i - 14)

def ntree8RRLRLRLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2802,by decide⟩,⟨2803,by decide⟩,⟨2804,by decide⟩] | 1 => ![⟨2805,by decide⟩,⟨2806,by decide⟩,⟨2807,by decide⟩] | 2 => ![⟨2808,by decide⟩,⟨1711,by decide⟩,⟨2809,by decide⟩] | 3 => ![⟨2810,by decide⟩,⟨2811,by decide⟩,⟨2810,by decide⟩] | 4 => ![⟨2812,by decide⟩,⟨2813,by decide⟩,⟨2798,by decide⟩] | 5 => ![⟨2814,by decide⟩,⟨2803,by decide⟩,⟨2815,by decide⟩] | _ => ![⟨2816,by decide⟩,⟨2803,by decide⟩,⟨2502,by decide⟩]

def ntree8RRLRLRLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2817,by decide⟩,⟨2818,by decide⟩,⟨2819,by decide⟩] | 1 => ![⟨2820,by decide⟩,⟨2821,by decide⟩,⟨2822,by decide⟩] | 2 => ![⟨2823,by decide⟩,⟨2821,by decide⟩,⟨2707,by decide⟩] | 3 => ![⟨2715,by decide⟩,⟨2824,by decide⟩,⟨2825,by decide⟩] | 4 => ![⟨2826,by decide⟩,⟨2827,by decide⟩,⟨2828,by decide⟩] | 5 => ![⟨2715,by decide⟩,⟨2829,by decide⟩,⟨2715,by decide⟩] | _ => ![⟨2830,by decide⟩,⟨2831,by decide⟩,⟨2832,by decide⟩]

def ntree8RRLRLRL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRLRLRLL i else ntree8RRLRLRLR (i - 7)

def ntree8RRLRLRRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2833,by decide⟩,⟨2834,by decide⟩,⟨2835,by decide⟩] | 1 => ![⟨2836,by decide⟩,⟨2837,by decide⟩,⟨2722,by decide⟩] | 2 => ![⟨2838,by decide⟩,⟨2839,by decide⟩,⟨2840,by decide⟩] | 3 => ![⟨2841,by decide⟩,⟨2842,by decide⟩,⟨2843,by decide⟩] | 4 => ![⟨2844,by decide⟩,⟨2842,by decide⟩,⟨2728,by decide⟩] | 5 => ![⟨2735,by decide⟩,⟨2845,by decide⟩,⟨2846,by decide⟩] | _ => ![⟨2847,by decide⟩,⟨2848,by decide⟩,⟨2849,by decide⟩]

def ntree8RRLRLRRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2735,by decide⟩,⟨2850,by decide⟩,⟨2735,by decide⟩] | 1 => ![⟨2851,by decide⟩,⟨2852,by decide⟩,⟨2853,by decide⟩] | 2 => ![⟨2854,by decide⟩,⟨2855,by decide⟩,⟨2856,by decide⟩] | 3 => ![⟨2857,by decide⟩,⟨2858,by decide⟩,⟨2741,by decide⟩] | 4 => ![⟨2859,by decide⟩,⟨2860,by decide⟩,⟨2861,by decide⟩] | 5 => ![⟨2862,by decide⟩,⟨2863,by decide⟩,⟨2822,by decide⟩] | _ => ![⟨2864,by decide⟩,⟨2863,by decide⟩,⟨2747,by decide⟩]

def ntree8RRLRLRR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRLRLRRL i else ntree8RRLRLRRR (i - 7)

def ntree8RRLRLR (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RRLRLRL i else ntree8RRLRLRR (i - 14)

def ntree8RRLRL (i : Nat) : Fin 3 → Fin 3321 := if i < 28 then ntree8RRLRLL i else ntree8RRLRLR (i - 28)

def ntree8RRLRRLLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2752,by decide⟩,⟨2865,by decide⟩,⟨2866,by decide⟩] | 1 => ![⟨2867,by decide⟩,⟨2868,by decide⟩,⟨2828,by decide⟩] | 2 => ![⟨2752,by decide⟩,⟨2869,by decide⟩,⟨2752,by decide⟩] | 3 => ![⟨2870,by decide⟩,⟨2871,by decide⟩,⟨2872,by decide⟩] | 4 => ![⟨2873,by decide⟩,⟨2874,by decide⟩,⟨2835,by decide⟩] | 5 => ![⟨2875,by decide⟩,⟨2876,by decide⟩,⟨2759,by decide⟩] | _ => ![⟨2877,by decide⟩,⟨2878,by decide⟩,⟨2879,by decide⟩]

def ntree8RRLRRLLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1770,by decide⟩,⟨2878,by decide⟩,⟨2880,by decide⟩] | 1 => ![⟨2881,by decide⟩,⟨2882,by decide⟩,⟨2883,by decide⟩] | 2 => ![⟨2884,by decide⟩,⟨2885,by decide⟩,⟨2886,by decide⟩] | 3 => ![⟨2887,by decide⟩,⟨2888,by decide⟩,⟨2725,by decide⟩] | 4 => ![⟨2889,by decide⟩,⟨2890,by decide⟩,⟨2722,by decide⟩] | 5 => ![⟨1780,by decide⟩,⟨2891,by decide⟩,⟨2724,by decide⟩] | _ => ![⟨2887,by decide⟩,⟨2892,by decide⟩,⟨2727,by decide⟩]

def ntree8RRLRRLL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRLRRLLL i else ntree8RRLRRLLR (i - 7)

def ntree8RRLRRLRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2893,by decide⟩,⟨1767,by decide⟩,⟨2894,by decide⟩] | 1 => ![⟨1767,by decide⟩,⟨1767,by decide⟩,⟨2895,by decide⟩] | 2 => ![⟨2896,by decide⟩,⟨2897,by decide⟩,⟨2898,by decide⟩] | 3 => ![⟨2899,by decide⟩,⟨2885,by decide⟩,⟨2900,by decide⟩] | 4 => ![⟨2901,by decide⟩,⟨2888,by decide⟩,⟨2744,by decide⟩] | 5 => ![⟨2902,by decide⟩,⟨2903,by decide⟩,⟨2741,by decide⟩] | _ => ![⟨1781,by decide⟩,⟨1781,by decide⟩,⟨2743,by decide⟩]

def ntree8RRLRRLRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2901,by decide⟩,⟨2904,by decide⟩,⟨2746,by decide⟩] | 1 => ![⟨2893,by decide⟩,⟨2878,by decide⟩,⟨2905,by decide⟩] | 2 => ![⟨1767,by decide⟩,⟨2878,by decide⟩,⟨2906,by decide⟩] | 3 => ![⟨2896,by decide⟩,⟨2882,by decide⟩,⟨2907,by decide⟩] | 4 => ![⟨2908,by decide⟩,⟨2909,by decide⟩,⟨2910,by decide⟩] | 5 => ![⟨2911,by decide⟩,⟨2912,by decide⟩,⟨2761,by decide⟩] | _ => ![⟨2913,by decide⟩,⟨2914,by decide⟩,⟨2759,by decide⟩]

def ntree8RRLRRLR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRLRRLRL i else ntree8RRLRRLRR (i - 7)

def ntree8RRLRRL (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RRLRRLL i else ntree8RRLRRLR (i - 14)

def ntree8RRLRRRLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1782,by decide⟩,⟨2915,by decide⟩,⟨430,by decide⟩] | 1 => ![⟨2911,by decide⟩,⟨2916,by decide⟩,⟨2763,by decide⟩] | 2 => ![⟨2917,by decide⟩,⟨2915,by decide⟩,⟨2505,by decide⟩] | 3 => ![⟨2877,by decide⟩,⟨1767,by decide⟩,⟨2918,by decide⟩] | 4 => ![⟨2919,by decide⟩,⟨1781,by decide⟩,⟨2507,by decide⟩] | 5 => ![⟨2920,by decide⟩,⟨2915,by decide⟩,⟨2921,by decide⟩] | _ => ![⟨1781,by decide⟩,⟨2891,by decide⟩,⟨2461,by decide⟩]

def ntree8RRLRRRLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2922,by decide⟩,⟨2891,by decide⟩,⟨2511,by decide⟩] | 1 => ![⟨2923,by decide⟩,⟨1843,by decide⟩,⟨2514,by decide⟩] | 2 => ![⟨2893,by decide⟩,⟨1826,by decide⟩,⟨2924,by decide⟩] | 3 => ![⟨2925,by decide⟩,⟨1830,by decide⟩,⟨2520,by decide⟩] | 4 => ![⟨2926,by decide⟩,⟨1936,by decide⟩,⟨2927,by decide⟩] | 5 => ![⟨2928,by decide⟩,⟨1830,by decide⟩,⟨2525,by decide⟩] | _ => ![⟨2929,by decide⟩,⟨2930,by decide⟩,⟨2931,by decide⟩]

def ntree8RRLRRRL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRLRRRLL i else ntree8RRLRRRLR (i - 7)

def ntree8RRLRRRRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2932,by decide⟩,⟨2933,by decide⟩,⟨2528,by decide⟩] | 1 => ![⟨2893,by decide⟩,⟨1767,by decide⟩,⟨2934,by decide⟩] | 2 => ![⟨2935,by decide⟩,⟨1843,by decide⟩,⟨2530,by decide⟩] | 3 => ![⟨2926,by decide⟩,⟨2915,by decide⟩,⟨2936,by decide⟩] | 4 => ![⟨2937,by decide⟩,⟨2933,by decide⟩,⟨280,by decide⟩] | 5 => ![⟨2938,by decide⟩,⟨2933,by decide⟩,⟨2533,by decide⟩] | _ => ![⟨2939,by decide⟩,⟨2940,by decide⟩,⟨2941,by decide⟩]

def ntree8RRLRRRRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2942,by decide⟩,⟨2915,by decide⟩,⟨2448,by decide⟩] | 1 => ![⟨2889,by decide⟩,⟨2943,by decide⟩,⟨2944,by decide⟩] | 2 => ![⟨2889,by decide⟩,⟨2945,by decide⟩,⟨2946,by decide⟩] | 3 => ![⟨2947,by decide⟩,⟨2948,by decide⟩,⟨2949,by decide⟩] | 4 => ![⟨2950,by decide⟩,⟨2951,by decide⟩,⟨2952,by decide⟩] | 5 => ![⟨2953,by decide⟩,⟨1843,by decide⟩,⟨2954,by decide⟩] | 6 => ![⟨2902,by decide⟩,⟨2955,by decide⟩,⟨2956,by decide⟩] | _ => ![⟨2902,by decide⟩,⟨2957,by decide⟩,⟨2958,by decide⟩]

def ntree8RRLRRRR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRLRRRRL i else ntree8RRLRRRRR (i - 7)

def ntree8RRLRRR (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RRLRRRL i else ntree8RRLRRRR (i - 14)

def ntree8RRLRR (i : Nat) : Fin 3 → Fin 3321 := if i < 28 then ntree8RRLRRL i else ntree8RRLRRR (i - 28)

def ntree8RRLR (i : Nat) : Fin 3 → Fin 3321 := if i < 56 then ntree8RRLRL i else ntree8RRLRR (i - 56)

def ntree8RRL (i : Nat) : Fin 3 → Fin 3321 := if i < 113 then ntree8RRLL i else ntree8RRLR (i - 113)

def ntree8RRRLLLLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2959,by decide⟩,⟨1843,by decide⟩,⟨706,by decide⟩] | 1 => ![⟨2960,by decide⟩,⟨2961,by decide⟩,⟨2962,by decide⟩] | 2 => ![⟨2963,by decide⟩,⟨2964,by decide⟩,⟨2965,by decide⟩] | 3 => ![⟨2913,by decide⟩,⟨2966,by decide⟩,⟨2967,by decide⟩] | 4 => ![⟨2913,by decide⟩,⟨2968,by decide⟩,⟨2969,by decide⟩] | 5 => ![⟨2970,by decide⟩,⟨2933,by decide⟩,⟨720,by decide⟩] | _ => ![⟨2971,by decide⟩,⟨2972,by decide⟩,⟨2973,by decide⟩]

def ntree8RRRLLLLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2974,by decide⟩,⟨2975,by decide⟩,⟨2976,by decide⟩] | 1 => ![⟨2977,by decide⟩,⟨2975,by decide⟩,⟨2978,by decide⟩] | 2 => ![⟨2979,by decide⟩,⟨2980,by decide⟩,⟨2710,by decide⟩] | 3 => ![⟨2981,by decide⟩,⟨2982,by decide⟩,⟨2715,by decide⟩] | 4 => ![⟨2983,by decide⟩,⟨2984,by decide⟩,⟨2717,by decide⟩] | 5 => ![⟨2985,by decide⟩,⟨2986,by decide⟩,⟨2718,by decide⟩] | _ => ![⟨2889,by decide⟩,⟨2987,by decide⟩,⟨2988,by decide⟩]

def ntree8RRRLLLL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRRLLLLL i else ntree8RRRLLLLR (i - 7)

def ntree8RRRLLLRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2989,by decide⟩,⟨2990,by decide⟩,⟨2991,by decide⟩] | 1 => ![⟨2992,by decide⟩,⟨2990,by decide⟩,⟨2993,by decide⟩] | 2 => ![⟨2994,by decide⟩,⟨2980,by decide⟩,⟨2731,by decide⟩] | 3 => ![⟨2995,by decide⟩,⟨2982,by decide⟩,⟨2735,by decide⟩] | 4 => ![⟨2996,by decide⟩,⟨2984,by decide⟩,⟨2737,by decide⟩] | 5 => ![⟨2997,by decide⟩,⟨2986,by decide⟩,⟨2738,by decide⟩] | _ => ![⟨2902,by decide⟩,⟨2998,by decide⟩,⟨2999,by decide⟩]

def ntree8RRRLLLRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2989,by decide⟩,⟨2975,by decide⟩,⟨3000,by decide⟩] | 1 => ![⟨2992,by decide⟩,⟨2975,by decide⟩,⟨3001,by decide⟩] | 2 => ![⟨3002,by decide⟩,⟨3003,by decide⟩,⟨2752,by decide⟩] | 3 => ![⟨3004,by decide⟩,⟨3005,by decide⟩,⟨2754,by decide⟩] | 4 => ![⟨3006,by decide⟩,⟨3007,by decide⟩,⟨2755,by decide⟩] | 5 => ![⟨2913,by decide⟩,⟨3008,by decide⟩,⟨3009,by decide⟩] | _ => ![⟨3010,by decide⟩,⟨3011,by decide⟩,⟨3012,by decide⟩]

def ntree8RRRLLLR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRRLLLRL i else ntree8RRRLLLRR (i - 7)

def ntree8RRRLLL (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RRRLLLL i else ntree8RRRLLLR (i - 14)

def ntree8RRRLLRLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3013,by decide⟩,⟨3014,by decide⟩,⟨3015,by decide⟩] | 1 => ![⟨3016,by decide⟩,⟨3017,by decide⟩,⟨3018,by decide⟩] | 2 => ![⟨3019,by decide⟩,⟨3017,by decide⟩,⟨3020,by decide⟩] | 3 => ![⟨3021,by decide⟩,⟨1781,by decide⟩,⟨3022,by decide⟩] | 4 => ![⟨3023,by decide⟩,⟨3024,by decide⟩,⟨3025,by decide⟩] | 5 => ![⟨3010,by decide⟩,⟨3026,by decide⟩,⟨3027,by decide⟩] | _ => ![⟨3028,by decide⟩,⟨3026,by decide⟩,⟨3029,by decide⟩]

def ntree8RRRLLRLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3030,by decide⟩,⟨1843,by decide⟩,⟨3031,by decide⟩] | 1 => ![⟨3032,by decide⟩,⟨1843,by decide⟩,⟨3033,by decide⟩] | 2 => ![⟨3034,by decide⟩,⟨1936,by decide⟩,⟨3035,by decide⟩] | 3 => ![⟨3036,by decide⟩,⟨1830,by decide⟩,⟨3037,by decide⟩] | 4 => ![⟨3038,by decide⟩,⟨1830,by decide⟩,⟨3039,by decide⟩] | 5 => ![⟨3028,by decide⟩,⟨3040,by decide⟩,⟨3041,by decide⟩] | _ => ![⟨3042,by decide⟩,⟨3014,by decide⟩,⟨3043,by decide⟩]

def ntree8RRRLLRL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRRLLRLL i else ntree8RRRLLRLR (i - 7)

def ntree8RRRLLRRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3044,by decide⟩,⟨3045,by decide⟩,⟨3046,by decide⟩] | 1 => ![⟨3047,by decide⟩,⟨3048,by decide⟩,⟨3049,by decide⟩] | 2 => ![⟨3050,by decide⟩,⟨1843,by decide⟩,⟨3051,by decide⟩] | 3 => ![⟨3052,by decide⟩,⟨3053,by decide⟩,⟨3054,by decide⟩] | 4 => ![⟨3042,by decide⟩,⟨3055,by decide⟩,⟨3056,by decide⟩] | 5 => ![⟨3057,by decide⟩,⟨3058,by decide⟩,⟨2817,by decide⟩] | _ => ![⟨3059,by decide⟩,⟨3060,by decide⟩,⟨3061,by decide⟩]

def ntree8RRRLLRRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2974,by decide⟩,⟨3060,by decide⟩,⟨2686,by decide⟩] | 1 => ![⟨3062,by decide⟩,⟨3060,by decide⟩,⟨3063,by decide⟩] | 2 => ![⟨2981,by decide⟩,⟨3064,by decide⟩,⟨3065,by decide⟩] | 3 => ![⟨3066,by decide⟩,⟨3067,by decide⟩,⟨2830,by decide⟩] | 4 => ![⟨3068,by decide⟩,⟨3058,by decide⟩,⟨2838,by decide⟩] | 5 => ![⟨3069,by decide⟩,⟨3070,by decide⟩,⟨3071,by decide⟩] | _ => ![⟨2989,by decide⟩,⟨3070,by decide⟩,⟨2696,by decide⟩]

def ntree8RRRLLRR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRRLLRRL i else ntree8RRRLLRRR (i - 7)

def ntree8RRRLLR (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RRRLLRL i else ntree8RRRLLRR (i - 14)

def ntree8RRRLL (i : Nat) : Fin 3 → Fin 3321 := if i < 28 then ntree8RRRLLL i else ntree8RRRLLR (i - 28)

def ntree8RRRLRLLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3072,by decide⟩,⟨3070,by decide⟩,⟨3073,by decide⟩] | 1 => ![⟨2995,by decide⟩,⟨3074,by decide⟩,⟨3075,by decide⟩] | 2 => ![⟨3076,by decide⟩,⟨3067,by decide⟩,⟨2851,by decide⟩] | 3 => ![⟨3077,by decide⟩,⟨3078,by decide⟩,⟨2859,by decide⟩] | 4 => ![⟨3059,by decide⟩,⟨3070,by decide⟩,⟨3079,by decide⟩] | 5 => ![⟨3062,by decide⟩,⟨3070,by decide⟩,⟨3080,by decide⟩] | _ => ![⟨3002,by decide⟩,⟨3081,by decide⟩,⟨3082,by decide⟩]

def ntree8RRRLRLLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3083,by decide⟩,⟨3084,by decide⟩,⟨2870,by decide⟩] | 1 => ![⟨3085,by decide⟩,⟨2310,by decide⟩,⟨2310,by decide⟩] | 2 => ![⟨3086,by decide⟩,⟨3087,by decide⟩,⟨2709,by decide⟩] | 3 => ![⟨3088,by decide⟩,⟨2310,by decide⟩,⟨3089,by decide⟩] | 4 => ![⟨3090,by decide⟩,⟨3091,by decide⟩,⟨3092,by decide⟩] | 5 => ![⟨2717,by decide⟩,⟨3093,by decide⟩,⟨2717,by decide⟩] | _ => ![⟨2717,by decide⟩,⟨2317,by decide⟩,⟨3094,by decide⟩]

def ntree8RRRLRLL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRRLRLLL i else ntree8RRRLRLLR (i - 7)

def ntree8RRRLRLRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1642,by decide⟩,⟨2461,by decide⟩,⟨2724,by decide⟩] | 1 => ![⟨1992,by decide⟩,⟨2326,by decide⟩,⟨3095,by decide⟩] | 2 => ![⟨3096,by decide⟩,⟨2335,by decide⟩,⟨2335,by decide⟩] | 3 => ![⟨3097,by decide⟩,⟨3098,by decide⟩,⟨2730,by decide⟩] | 4 => ![⟨3099,by decide⟩,⟨2335,by decide⟩,⟨3100,by decide⟩] | 5 => ![⟨3101,by decide⟩,⟨3102,by decide⟩,⟨3103,by decide⟩] | _ => ![⟨2737,by decide⟩,⟨3104,by decide⟩,⟨2737,by decide⟩]

def ntree8RRRLRLRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨2737,by decide⟩,⟨2340,by decide⟩,⟨3105,by decide⟩] | 1 => ![⟨3106,by decide⟩,⟨3107,by decide⟩,⟨881,by decide⟩] | 2 => ![⟨3108,by decide⟩,⟨3109,by decide⟩,⟨2743,by decide⟩] | 3 => ![⟨1214,by decide⟩,⟨1214,by decide⟩,⟨3110,by decide⟩] | 4 => ![⟨3111,by decide⟩,⟨2354,by decide⟩,⟨2354,by decide⟩] | 5 => ![⟨3112,by decide⟩,⟨3113,by decide⟩,⟨2748,by decide⟩] | _ => ![⟨3114,by decide⟩,⟨2354,by decide⟩,⟨3115,by decide⟩]

def ntree8RRRLRLR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRRLRLRL i else ntree8RRRLRLRR (i - 7)

def ntree8RRRLRL (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RRRLRLL i else ntree8RRRLRLR (i - 14)

def ntree8RRRLRRLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3116,by decide⟩,⟨3117,by decide⟩,⟨3118,by decide⟩] | 1 => ![⟨2754,by decide⟩,⟨3119,by decide⟩,⟨2754,by decide⟩] | 2 => ![⟨2754,by decide⟩,⟨2358,by decide⟩,⟨3120,by decide⟩] | 3 => ![⟨3121,by decide⟩,⟨3122,by decide⟩,⟨430,by decide⟩] | 4 => ![⟨3123,by decide⟩,⟨3124,by decide⟩,⟨430,by decide⟩] | 5 => ![⟨2017,by decide⟩,⟨2367,by decide⟩,⟨3125,by decide⟩] | _ => ![⟨3126,by decide⟩,⟨57,by decide⟩,⟨57,by decide⟩]

def ntree8RRRLRRLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3127,by decide⟩,⟨60,by decide⟩,⟨901,by decide⟩] | 1 => ![⟨3128,by decide⟩,⟨16,by decide⟩,⟨904,by decide⟩] | 2 => ![⟨3129,by decide⟩,⟨64,by decide⟩,⟨3130,by decide⟩] | 3 => ![⟨3131,by decide⟩,⟨2397,by decide⟩,⟨3131,by decide⟩] | 4 => ![⟨3132,by decide⟩,⟨3133,by decide⟩,⟨3134,by decide⟩] | 5 => ![⟨1214,by decide⟩,⟨2326,by decide⟩,⟨2326,by decide⟩] | _ => ![⟨3135,by decide⟩,⟨70,by decide⟩,⟨70,by decide⟩]

def ntree8RRRLRRL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRRLRRLL i else ntree8RRRLRRLR (i - 7)

def ntree8RRRLRRRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3136,by decide⟩,⟨3137,by decide⟩,⟨919,by decide⟩] | 1 => ![⟨3138,by decide⟩,⟨3139,by decide⟩,⟨922,by decide⟩] | 2 => ![⟨3140,by decide⟩,⟨3141,by decide⟩,⟨3142,by decide⟩] | 3 => ![⟨3143,by decide⟩,⟨3144,by decide⟩,⟨3143,by decide⟩] | 4 => ![⟨3145,by decide⟩,⟨1695,by decide⟩,⟨3146,by decide⟩] | 5 => ![⟨70,by decide⟩,⟨3147,by decide⟩,⟨70,by decide⟩] | _ => ![⟨2397,by decide⟩,⟨3144,by decide⟩,⟨2397,by decide⟩]

def ntree8RRRLRRRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1214,by decide⟩,⟨3148,by decide⟩,⟨1214,by decide⟩] | 1 => ![⟨3149,by decide⟩,⟨60,by decide⟩,⟨60,by decide⟩] | 2 => ![⟨3150,by decide⟩,⟨3151,by decide⟩,⟨936,by decide⟩] | 3 => ![⟨3152,by decide⟩,⟨2803,by decide⟩,⟨939,by decide⟩] | 4 => ![⟨3153,by decide⟩,⟨3154,by decide⟩,⟨3155,by decide⟩] | 5 => ![⟨3156,by decide⟩,⟨3137,by decide⟩,⟨3156,by decide⟩] | 6 => ![⟨3157,by decide⟩,⟨3158,by decide⟩,⟨3159,by decide⟩] | _ => ![⟨3160,by decide⟩,⟨3161,by decide⟩,⟨60,by decide⟩]

def ntree8RRRLRRR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRRLRRRL i else ntree8RRRLRRRR (i - 7)

def ntree8RRRLRR (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RRRLRRL i else ntree8RRRLRRR (i - 14)

def ntree8RRRLR (i : Nat) : Fin 3 → Fin 3321 := if i < 28 then ntree8RRRLRL i else ntree8RRRLRR (i - 28)

def ntree8RRRL (i : Nat) : Fin 3 → Fin 3321 := if i < 56 then ntree8RRRLL i else ntree8RRRLR (i - 56)

def ntree8RRRRLLLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3162,by decide⟩,⟨3151,by decide⟩,⟨60,by decide⟩] | 1 => ![⟨3163,by decide⟩,⟨3164,by decide⟩,⟨2367,by decide⟩] | 2 => ![⟨2677,by decide⟩,⟨2410,by decide⟩,⟨2410,by decide⟩] | 3 => ![⟨3165,by decide⟩,⟨3166,by decide⟩,⟨2413,by decide⟩] | 4 => ![⟨3167,by decide⟩,⟨3168,by decide⟩,⟨2310,by decide⟩] | 5 => ![⟨3169,by decide⟩,⟨2416,by decide⟩,⟨3170,by decide⟩] | _ => ![⟨3169,by decide⟩,⟨3171,by decide⟩,⟨3169,by decide⟩]

def ntree8RRRRLLLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3172,by decide⟩,⟨3173,by decide⟩,⟨3092,by decide⟩] | 1 => ![⟨2677,by decide⟩,⟨2425,by decide⟩,⟨2425,by decide⟩] | 2 => ![⟨3165,by decide⟩,⟨3174,by decide⟩,⟨2428,by decide⟩] | 3 => ![⟨3167,by decide⟩,⟨3175,by decide⟩,⟨2335,by decide⟩] | 4 => ![⟨3176,by decide⟩,⟨2431,by decide⟩,⟨3177,by decide⟩] | 5 => ![⟨3176,by decide⟩,⟨3178,by decide⟩,⟨3176,by decide⟩] | _ => ![⟨3179,by decide⟩,⟨3180,by decide⟩,⟨3103,by decide⟩]

def ntree8RRRRLLL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRRRLLLL i else ntree8RRRRLLLR (i - 7)

def ntree8RRRRLLRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3181,by decide⟩,⟨3137,by decide⟩,⟨974,by decide⟩] | 1 => ![⟨3182,by decide⟩,⟨3139,by decide⟩,⟨881,by decide⟩] | 2 => ![⟨2699,by decide⟩,⟨2438,by decide⟩,⟨2438,by decide⟩] | 3 => ![⟨3183,by decide⟩,⟨3184,by decide⟩,⟨2413,by decide⟩] | 4 => ![⟨3185,by decide⟩,⟨3186,by decide⟩,⟨2354,by decide⟩] | 5 => ![⟨3169,by decide⟩,⟨2431,by decide⟩,⟨3187,by decide⟩] | _ => ![⟨3169,by decide⟩,⟨3178,by decide⟩,⟨3169,by decide⟩]

def ntree8RRRRLLRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3172,by decide⟩,⟨3180,by decide⟩,⟨3118,by decide⟩] | 1 => ![⟨3188,by decide⟩,⟨3151,by decide⟩,⟨964,by decide⟩] | 2 => ![⟨3189,by decide⟩,⟨2803,by decide⟩,⟨430,by decide⟩] | 3 => ![⟨3190,by decide⟩,⟨3191,by decide⟩,⟨3192,by decide⟩] | 4 => ![⟨1772,by decide⟩,⟨2915,by decide⟩,⟨3193,by decide⟩] | 5 => ![⟨3194,by decide⟩,⟨3191,by decide⟩,⟨3195,by decide⟩] | _ => ![⟨3196,by decide⟩,⟨3197,by decide⟩,⟨3198,by decide⟩]

def ntree8RRRRLLR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRRRLLRL i else ntree8RRRRLLRR (i - 7)

def ntree8RRRRLL (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RRRRLLL i else ntree8RRRRLLR (i - 14)

def ntree8RRRRLRLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3199,by decide⟩,⟨3200,by decide⟩,⟨3201,by decide⟩] | 1 => ![⟨3202,by decide⟩,⟨3203,by decide⟩,⟨3204,by decide⟩] | 2 => ![⟨3205,by decide⟩,⟨3200,by decide⟩,⟨3206,by decide⟩] | 3 => ![⟨3207,by decide⟩,⟨3208,by decide⟩,⟨3209,by decide⟩] | 4 => ![⟨1781,by decide⟩,⟨3210,by decide⟩,⟨2475,by decide⟩] | 5 => ![⟨3211,by decide⟩,⟨3212,by decide⟩,⟨3213,by decide⟩] | _ => ![⟨3214,by decide⟩,⟨3210,by decide⟩,⟨3215,by decide⟩]

def ntree8RRRRLRLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3216,by decide⟩,⟨3217,by decide⟩,⟨3218,by decide⟩] | 1 => ![⟨3219,by decide⟩,⟨3220,by decide⟩,⟨175,by decide⟩] | 2 => ![⟨3221,by decide⟩,⟨3217,by decide⟩,⟨3222,by decide⟩] | 3 => ![⟨3223,by decide⟩,⟨3224,by decide⟩,⟨3225,by decide⟩] | 4 => ![⟨1782,by decide⟩,⟨3203,by decide⟩,⟨3226,by decide⟩] | 5 => ![⟨3227,by decide⟩,⟨3220,by decide⟩,⟨3228,by decide⟩] | _ => ![⟨3229,by decide⟩,⟨3230,by decide⟩,⟨1045,by decide⟩]

def ntree8RRRRLRL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRRRLRLL i else ntree8RRRRLRLR (i - 7)

def ntree8RRRRLRRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3231,by decide⟩,⟨3230,by decide⟩,⟨60,by decide⟩] | 1 => ![⟨3232,by decide⟩,⟨2915,by decide⟩,⟨1049,by decide⟩] | 2 => ![⟨3229,by decide⟩,⟨3231,by decide⟩,⟨3233,by decide⟩] | 3 => ![⟨3234,by decide⟩,⟨3234,by decide⟩,⟨2397,by decide⟩] | 4 => ![⟨3234,by decide⟩,⟨3235,by decide⟩,⟨2383,by decide⟩] | 5 => ![⟨3236,by decide⟩,⟨3231,by decide⟩,⟨1062,by decide⟩] | _ => ![⟨3231,by decide⟩,⟨3237,by decide⟩,⟨211,by decide⟩]

def ntree8RRRRLRRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3238,by decide⟩,⟨1843,by decide⟩,⟨1065,by decide⟩] | 1 => ![⟨3236,by decide⟩,⟨3239,by decide⟩,⟨3240,by decide⟩] | 2 => ![⟨3234,by decide⟩,⟨3241,by decide⟩,⟨2518,by decide⟩] | 3 => ![⟨3231,by decide⟩,⟨3239,by decide⟩,⟨2522,by decide⟩] | 4 => ![⟨3236,by decide⟩,⟨3230,by decide⟩,⟨1073,by decide⟩] | 5 => ![⟨3242,by decide⟩,⟨3243,by decide⟩,⟨229,by decide⟩] | 6 => ![⟨3244,by decide⟩,⟨2933,by decide⟩,⟨1077,by decide⟩] | _ => ![⟨3236,by decide⟩,⟨3231,by decide⟩,⟨3245,by decide⟩]

def ntree8RRRRLRR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRRRLRRL i else ntree8RRRRLRRR (i - 7)

def ntree8RRRRLR (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RRRRLRL i else ntree8RRRRLRR (i - 14)

def ntree8RRRRL (i : Nat) : Fin 3 → Fin 3321 := if i < 28 then ntree8RRRRLL i else ntree8RRRRLR (i - 28)

def ntree8RRRRRLLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3246,by decide⟩,⟨3247,by decide⟩,⟨2535,by decide⟩] | 1 => ![⟨3248,by decide⟩,⟨3249,by decide⟩,⟨2540,by decide⟩] | 2 => ![⟨3250,by decide⟩,⟨3251,by decide⟩,⟨3252,by decide⟩] | 3 => ![⟨3250,by decide⟩,⟨3231,by decide⟩,⟨980,by decide⟩] | 4 => ![⟨3250,by decide⟩,⟨3230,by decide⟩,⟨964,by decide⟩] | 5 => ![⟨3246,by decide⟩,⟨3253,by decide⟩,⟨2553,by decide⟩] | _ => ![⟨3248,by decide⟩,⟨3254,by decide⟩,⟨2558,by decide⟩]

def ntree8RRRRRLLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3231,by decide⟩,⟨3255,by decide⟩,⟨3256,by decide⟩] | 1 => ![⟨3231,by decide⟩,⟨3231,by decide⟩,⟨974,by decide⟩] | 2 => ![⟨3257,by decide⟩,⟨3237,by decide⟩,⟨1107,by decide⟩] | 3 => ![⟨3258,by decide⟩,⟨3259,by decide⟩,⟨2570,by decide⟩] | 4 => ![⟨3260,by decide⟩,⟨3261,by decide⟩,⟨2573,by decide⟩] | 5 => ![⟨3250,by decide⟩,⟨3255,by decide⟩,⟨3262,by decide⟩] | _ => ![⟨3250,by decide⟩,⟨3237,by decide⟩,⟨1112,by decide⟩]

def ntree8RRRRRLL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRRRRLLL i else ntree8RRRRRLLR (i - 7)

def ntree8RRRRRLRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3263,by decide⟩,⟨3243,by decide⟩,⟨1114,by decide⟩] | 1 => ![⟨3264,by decide⟩,⟨3264,by decide⟩,⟨3265,by decide⟩] | 2 => ![⟨2977,by decide⟩,⟨3266,by decide⟩,⟨3267,by decide⟩] | 3 => ![⟨3268,by decide⟩,⟨3264,by decide⟩,⟨3088,by decide⟩] | 4 => ![⟨3062,by decide⟩,⟨3269,by decide⟩,⟨3270,by decide⟩] | 5 => ![⟨2983,by decide⟩,⟨3271,by decide⟩,⟨3272,by decide⟩] | _ => ![⟨2992,by decide⟩,⟨3273,by decide⟩,⟨3274,by decide⟩]

def ntree8RRRRRLRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3275,by decide⟩,⟨3264,by decide⟩,⟨3099,by decide⟩] | 1 => ![⟨3072,by decide⟩,⟨3276,by decide⟩,⟨3277,by decide⟩] | 2 => ![⟨2996,by decide⟩,⟨3278,by decide⟩,⟨3279,by decide⟩] | 3 => ![⟨2253,by decide⟩,⟨3280,by decide⟩,⟨3281,by decide⟩] | 4 => ![⟨3282,by decide⟩,⟨3282,by decide⟩,⟨3283,by decide⟩] | 5 => ![⟨3284,by decide⟩,⟨3282,by decide⟩,⟨3114,by decide⟩] | _ => ![⟨3004,by decide⟩,⟨3285,by decide⟩,⟨3286,by decide⟩]

def ntree8RRRRRLR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRRRRLRL i else ntree8RRRRRLRR (i - 7)

def ntree8RRRRRL (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RRRRRLL i else ntree8RRRRRLR (i - 14)

def ntree8RRRRRRLL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨1782,by decide⟩,⟨3287,by decide⟩,⟨3288,by decide⟩] | 1 => ![⟨3289,by decide⟩,⟨3289,by decide⟩,⟨1151,by decide⟩] | 2 => ![⟨3290,by decide⟩,⟨3231,by decide⟩,⟨1153,by decide⟩] | 3 => ![⟨3291,by decide⟩,⟨2253,by decide⟩,⟨1156,by decide⟩] | 4 => ![⟨3292,by decide⟩,⟨3231,by decide⟩,⟨3293,by decide⟩] | 5 => ![⟨3294,by decide⟩,⟨3234,by decide⟩,⟨3295,by decide⟩] | _ => ![⟨3289,by decide⟩,⟨3289,by decide⟩,⟨70,by decide⟩]

def ntree8RRRRRRLR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3296,by decide⟩,⟨3237,by decide⟩,⟨1164,by decide⟩] | 1 => ![⟨3297,by decide⟩,⟨2274,by decide⟩,⟨1167,by decide⟩] | 2 => ![⟨3298,by decide⟩,⟨3239,by decide⟩,⟨3299,by decide⟩] | 3 => ![⟨3300,by decide⟩,⟨3241,by decide⟩,⟨3301,by decide⟩] | 4 => ![⟨3289,by decide⟩,⟨3302,by decide⟩,⟨2660,by decide⟩] | 5 => ![⟨3231,by decide⟩,⟨3231,by decide⟩,⟨1175,by decide⟩] | _ => ![⟨3303,by decide⟩,⟨1843,by decide⟩,⟨1178,by decide⟩]

def ntree8RRRRRRL (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRRRRRLL i else ntree8RRRRRRLR (i - 7)

def ntree8RRRRRRRL (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3304,by decide⟩,⟨3237,by decide⟩,⟨3305,by decide⟩] | 1 => ![⟨3231,by decide⟩,⟨3306,by decide⟩,⟨2673,by decide⟩] | 2 => ![⟨3307,by decide⟩,⟨3307,by decide⟩,⟨2677,by decide⟩] | 3 => ![⟨3308,by decide⟩,⟨3309,by decide⟩,⟨2678,by decide⟩] | 4 => ![⟨3264,by decide⟩,⟨3310,by decide⟩,⟨2680,by decide⟩] | 5 => ![⟨3311,by decide⟩,⟨3308,by decide⟩,⟨3169,by decide⟩] | _ => ![⟨3311,by decide⟩,⟨3309,by decide⟩,⟨3312,by decide⟩]

def ntree8RRRRRRRR (i : Nat) : Fin 3 → Fin 3321 := match i with | 0 => ![⟨3313,by decide⟩,⟨3289,by decide⟩,⟨961,by decide⟩] | 1 => ![⟨3308,by decide⟩,⟨3314,by decide⟩,⟨2689,by decide⟩] | 2 => ![⟨3264,by decide⟩,⟨3315,by decide⟩,⟨2691,by decide⟩] | 3 => ![⟨3316,by decide⟩,⟨3308,by decide⟩,⟨3176,by decide⟩] | 4 => ![⟨3316,by decide⟩,⟨3314,by decide⟩,⟨3317,by decide⟩] | 5 => ![⟨3318,by decide⟩,⟨3318,by decide⟩,⟨2699,by decide⟩] | 6 => ![⟨3282,by decide⟩,⟨3319,by decide⟩,⟨2701,by decide⟩] | _ => ![⟨3311,by decide⟩,⟨3314,by decide⟩,⟨3320,by decide⟩]

def ntree8RRRRRRR (i : Nat) : Fin 3 → Fin 3321 := if i < 7 then ntree8RRRRRRRL i else ntree8RRRRRRRR (i - 7)

def ntree8RRRRRR (i : Nat) : Fin 3 → Fin 3321 := if i < 14 then ntree8RRRRRRL i else ntree8RRRRRRR (i - 14)

def ntree8RRRRR (i : Nat) : Fin 3 → Fin 3321 := if i < 28 then ntree8RRRRRL i else ntree8RRRRRR (i - 28)

def ntree8RRRR (i : Nat) : Fin 3 → Fin 3321 := if i < 57 then ntree8RRRRL i else ntree8RRRRR (i - 57)

def ntree8RRR (i : Nat) : Fin 3 → Fin 3321 := if i < 113 then ntree8RRRL i else ntree8RRRR (i - 113)

def ntree8RR (i : Nat) : Fin 3 → Fin 3321 := if i < 226 then ntree8RRL i else ntree8RRR (i - 226)

def ntree8R (i : Nat) : Fin 3 → Fin 3321 := if i < 453 then ntree8RL i else ntree8RR (i - 453)

def ntree8 (i : Nat) : Fin 3 → Fin 3321 := if i < 906 then ntree8L i else ntree8R (i - 906)

def layer8 : Fin 3321 → State := fun i => stree8 i.val

def next8 : Fin 1812 → Fin 3 → Fin 3321 := fun i => ntree8 i.val

end Paper2.Certificates.Q6.Coverage
