import Paper2.Certificates.Q6CoverageCompact.Layer13Part004

namespace Paper2.Certificates.Q6.Coverage

def stree13RRLRLLRR (i : Nat) : State := match i with | 0 => state13_1717 | 1 => state13_1718 | 2 => state13_1719 | 3 => state13_1720 | 4 => state13_1721 | 5 => state13_1722 | 6 => state13_1723 | _ => state13_1724

def stree13RRLRLLR (i : Nat) : State := if i < 8 then stree13RRLRLLRL i else stree13RRLRLLRR (i - 8)

def stree13RRLRLL (i : Nat) : State := if i < 16 then stree13RRLRLLL i else stree13RRLRLLR (i - 16)

def stree13RRLRLRLL (i : Nat) : State := match i with | 0 => state13_1725 | 1 => state13_1726 | 2 => state13_1727 | 3 => state13_1728 | 4 => state13_1729 | 5 => state13_1730 | 6 => state13_1731 | _ => state13_1732

def stree13RRLRLRLR (i : Nat) : State := match i with | 0 => state13_1733 | 1 => state13_1734 | 2 => state13_1735 | 3 => state13_1736 | 4 => state13_1737 | 5 => state13_1738 | 6 => state13_1739 | _ => state13_1740

def stree13RRLRLRL (i : Nat) : State := if i < 8 then stree13RRLRLRLL i else stree13RRLRLRLR (i - 8)

def stree13RRLRLRRL (i : Nat) : State := match i with | 0 => state13_1741 | 1 => state13_1742 | 2 => state13_1743 | 3 => state13_1744 | 4 => state13_1745 | 5 => state13_1746 | 6 => state13_1747 | _ => state13_1748

def stree13RRLRLRRRL (i : Nat) : State := match i with | 0 => state13_1749 | 1 => state13_1750 | 2 => state13_1751 | _ => state13_1752

def stree13RRLRLRRRR (i : Nat) : State := match i with | 0 => state13_1753 | 1 => state13_1754 | 2 => state13_1755 | 3 => state13_1756 | _ => state13_1757

def stree13RRLRLRRR (i : Nat) : State := if i < 4 then stree13RRLRLRRRL i else stree13RRLRLRRRR (i - 4)

def stree13RRLRLRR (i : Nat) : State := if i < 8 then stree13RRLRLRRL i else stree13RRLRLRRR (i - 8)

def stree13RRLRLR (i : Nat) : State := if i < 16 then stree13RRLRLRL i else stree13RRLRLRR (i - 16)

def stree13RRLRL (i : Nat) : State := if i < 32 then stree13RRLRLL i else stree13RRLRLR (i - 32)

def stree13RRLRRLLL (i : Nat) : State := match i with | 0 => state13_1758 | 1 => state13_1759 | 2 => state13_1760 | 3 => state13_1761 | 4 => state13_1762 | 5 => state13_1763 | 6 => state13_1764 | _ => state13_1765

def stree13RRLRRLLR (i : Nat) : State := match i with | 0 => state13_1766 | 1 => state13_1767 | 2 => state13_1768 | 3 => state13_1769 | 4 => state13_1770 | 5 => state13_1771 | 6 => state13_1772 | _ => state13_1773

def stree13RRLRRLL (i : Nat) : State := if i < 8 then stree13RRLRRLLL i else stree13RRLRRLLR (i - 8)

def stree13RRLRRLRL (i : Nat) : State := match i with | 0 => state13_1774 | 1 => state13_1775 | 2 => state13_1776 | 3 => state13_1777 | 4 => state13_1778 | 5 => state13_1779 | 6 => state13_1780 | _ => state13_1781

def stree13RRLRRLRRL (i : Nat) : State := match i with | 0 => state13_1782 | 1 => state13_1783 | 2 => state13_1784 | _ => state13_1785

def stree13RRLRRLRRR (i : Nat) : State := match i with | 0 => state13_1786 | 1 => state13_1787 | 2 => state13_1788 | 3 => state13_1789 | _ => state13_1790

def stree13RRLRRLRR (i : Nat) : State := if i < 4 then stree13RRLRRLRRL i else stree13RRLRRLRRR (i - 4)

def stree13RRLRRLR (i : Nat) : State := if i < 8 then stree13RRLRRLRL i else stree13RRLRRLRR (i - 8)

def stree13RRLRRL (i : Nat) : State := if i < 16 then stree13RRLRRLL i else stree13RRLRRLR (i - 16)

def stree13RRLRRRLL (i : Nat) : State := match i with | 0 => state13_1791 | 1 => state13_1792 | 2 => state13_1793 | 3 => state13_1794 | 4 => state13_1795 | 5 => state13_1796 | 6 => state13_1797 | _ => state13_1798

def stree13RRLRRRLR (i : Nat) : State := match i with | 0 => state13_1799 | 1 => state13_1800 | 2 => state13_1801 | 3 => state13_1802 | 4 => state13_1803 | 5 => state13_1804 | 6 => state13_1805 | _ => state13_1806

def stree13RRLRRRL (i : Nat) : State := if i < 8 then stree13RRLRRRLL i else stree13RRLRRRLR (i - 8)

def stree13RRLRRRRL (i : Nat) : State := match i with | 0 => state13_1807 | 1 => state13_1808 | 2 => state13_1809 | 3 => state13_1810 | 4 => state13_1811 | 5 => state13_1812 | 6 => state13_1813 | _ => state13_1814

def stree13RRLRRRRRL (i : Nat) : State := match i with | 0 => state13_1815 | 1 => state13_1816 | 2 => state13_1817 | _ => state13_1818

def stree13RRLRRRRRR (i : Nat) : State := match i with | 0 => state13_1819 | 1 => state13_1820 | 2 => state13_1821 | 3 => state13_1822 | _ => state13_1823

def stree13RRLRRRRR (i : Nat) : State := if i < 4 then stree13RRLRRRRRL i else stree13RRLRRRRRR (i - 4)

def stree13RRLRRRR (i : Nat) : State := if i < 8 then stree13RRLRRRRL i else stree13RRLRRRRR (i - 8)

def stree13RRLRRR (i : Nat) : State := if i < 16 then stree13RRLRRRL i else stree13RRLRRRR (i - 16)

def stree13RRLRR (i : Nat) : State := if i < 33 then stree13RRLRRL i else stree13RRLRRR (i - 33)

def stree13RRLR (i : Nat) : State := if i < 65 then stree13RRLRL i else stree13RRLRR (i - 65)

def stree13RRL (i : Nat) : State := if i < 130 then stree13RRLL i else stree13RRLR (i - 130)

def stree13RRRLLLLL (i : Nat) : State := match i with | 0 => state13_1824 | 1 => state13_1825 | 2 => state13_1826 | 3 => state13_1827 | 4 => state13_1828 | 5 => state13_1829 | 6 => state13_1830 | _ => state13_1831

def stree13RRRLLLLR (i : Nat) : State := match i with | 0 => state13_1832 | 1 => state13_1833 | 2 => state13_1834 | 3 => state13_1835 | 4 => state13_1836 | 5 => state13_1837 | 6 => state13_1838 | _ => state13_1839

def stree13RRRLLLL (i : Nat) : State := if i < 8 then stree13RRRLLLLL i else stree13RRRLLLLR (i - 8)

def stree13RRRLLLRL (i : Nat) : State := match i with | 0 => state13_1840 | 1 => state13_1841 | 2 => state13_1842 | 3 => state13_1843 | 4 => state13_1844 | 5 => state13_1845 | 6 => state13_1846 | _ => state13_1847

def stree13RRRLLLRR (i : Nat) : State := match i with | 0 => state13_1848 | 1 => state13_1849 | 2 => state13_1850 | 3 => state13_1851 | 4 => state13_1852 | 5 => state13_1853 | 6 => state13_1854 | _ => state13_1855

def stree13RRRLLLR (i : Nat) : State := if i < 8 then stree13RRRLLLRL i else stree13RRRLLLRR (i - 8)

def stree13RRRLLL (i : Nat) : State := if i < 16 then stree13RRRLLLL i else stree13RRRLLLR (i - 16)

def stree13RRRLLRLL (i : Nat) : State := match i with | 0 => state13_1856 | 1 => state13_1857 | 2 => state13_1858 | 3 => state13_1859 | 4 => state13_1860 | 5 => state13_1861 | 6 => state13_1862 | _ => state13_1863

def stree13RRRLLRLR (i : Nat) : State := match i with | 0 => state13_1864 | 1 => state13_1865 | 2 => state13_1866 | 3 => state13_1867 | 4 => state13_1868 | 5 => state13_1869 | 6 => state13_1870 | _ => state13_1871

def stree13RRRLLRL (i : Nat) : State := if i < 8 then stree13RRRLLRLL i else stree13RRRLLRLR (i - 8)

def stree13RRRLLRRL (i : Nat) : State := match i with | 0 => state13_1872 | 1 => state13_1873 | 2 => state13_1874 | 3 => state13_1875 | 4 => state13_1876 | 5 => state13_1877 | 6 => state13_1878 | _ => state13_1879

def stree13RRRLLRRRL (i : Nat) : State := match i with | 0 => state13_1880 | 1 => state13_1881 | 2 => state13_1882 | _ => state13_1883

def stree13RRRLLRRRR (i : Nat) : State := match i with | 0 => state13_1884 | 1 => state13_1885 | 2 => state13_1886 | 3 => state13_1887 | _ => state13_1888

def stree13RRRLLRRR (i : Nat) : State := if i < 4 then stree13RRRLLRRRL i else stree13RRRLLRRRR (i - 4)

def stree13RRRLLRR (i : Nat) : State := if i < 8 then stree13RRRLLRRL i else stree13RRRLLRRR (i - 8)

def stree13RRRLLR (i : Nat) : State := if i < 16 then stree13RRRLLRL i else stree13RRRLLRR (i - 16)

def stree13RRRLL (i : Nat) : State := if i < 32 then stree13RRRLLL i else stree13RRRLLR (i - 32)

def stree13RRRLRLLL (i : Nat) : State := match i with | 0 => state13_1889 | 1 => state13_1890 | 2 => state13_1891 | 3 => state13_1892 | 4 => state13_1893 | 5 => state13_1894 | 6 => state13_1895 | _ => state13_1896

def stree13RRRLRLLR (i : Nat) : State := match i with | 0 => state13_1897 | 1 => state13_1898 | 2 => state13_1899 | 3 => state13_1900 | 4 => state13_1901 | 5 => state13_1902 | 6 => state13_1903 | _ => state13_1904

def stree13RRRLRLL (i : Nat) : State := if i < 8 then stree13RRRLRLLL i else stree13RRRLRLLR (i - 8)

def stree13RRRLRLRL (i : Nat) : State := match i with | 0 => state13_1905 | 1 => state13_1906 | 2 => state13_1907 | 3 => state13_1908 | 4 => state13_1909 | 5 => state13_1910 | 6 => state13_1911 | _ => state13_1912

def stree13RRRLRLRR (i : Nat) : State := match i with | 0 => state13_1913 | 1 => state13_1914 | 2 => state13_1915 | 3 => state13_1916 | 4 => state13_1917 | 5 => state13_1918 | 6 => state13_1919 | _ => state13_1920

def stree13RRRLRLR (i : Nat) : State := if i < 8 then stree13RRRLRLRL i else stree13RRRLRLRR (i - 8)

def stree13RRRLRL (i : Nat) : State := if i < 16 then stree13RRRLRLL i else stree13RRRLRLR (i - 16)

def stree13RRRLRRLL (i : Nat) : State := match i with | 0 => state13_1921 | 1 => state13_1922 | 2 => state13_1923 | 3 => state13_1924 | 4 => state13_1925 | 5 => state13_1926 | 6 => state13_1927 | _ => state13_1928

def stree13RRRLRRLR (i : Nat) : State := match i with | 0 => state13_1929 | 1 => state13_1930 | 2 => state13_1931 | 3 => state13_1932 | 4 => state13_1933 | 5 => state13_1934 | 6 => state13_1935 | _ => state13_1936

def stree13RRRLRRL (i : Nat) : State := if i < 8 then stree13RRRLRRLL i else stree13RRRLRRLR (i - 8)

def stree13RRRLRRRL (i : Nat) : State := match i with | 0 => state13_1937 | 1 => state13_1938 | 2 => state13_1939 | 3 => state13_1940 | 4 => state13_1941 | 5 => state13_1942 | 6 => state13_1943 | _ => state13_1944

def stree13RRRLRRRRL (i : Nat) : State := match i with | 0 => state13_1945 | 1 => state13_1946 | 2 => state13_1947 | _ => state13_1948

def stree13RRRLRRRRR (i : Nat) : State := match i with | 0 => state13_1949 | 1 => state13_1950 | 2 => state13_1951 | 3 => state13_1952 | _ => state13_1953

def stree13RRRLRRRR (i : Nat) : State := if i < 4 then stree13RRRLRRRRL i else stree13RRRLRRRRR (i - 4)

def stree13RRRLRRR (i : Nat) : State := if i < 8 then stree13RRRLRRRL i else stree13RRRLRRRR (i - 8)

def stree13RRRLRR (i : Nat) : State := if i < 16 then stree13RRRLRRL i else stree13RRRLRRR (i - 16)

def stree13RRRLR (i : Nat) : State := if i < 32 then stree13RRRLRL i else stree13RRRLRR (i - 32)

def stree13RRRL (i : Nat) : State := if i < 65 then stree13RRRLL i else stree13RRRLR (i - 65)

def stree13RRRRLLLL (i : Nat) : State := match i with | 0 => state13_1954 | 1 => state13_1955 | 2 => state13_1956 | 3 => state13_1957 | 4 => state13_1958 | 5 => state13_1959 | 6 => state13_1960 | _ => state13_1961

def stree13RRRRLLLR (i : Nat) : State := match i with | 0 => state13_1962 | 1 => state13_1963 | 2 => state13_1964 | 3 => state13_1965 | 4 => state13_1966 | 5 => state13_1967 | 6 => state13_1968 | _ => state13_1969

def stree13RRRRLLL (i : Nat) : State := if i < 8 then stree13RRRRLLLL i else stree13RRRRLLLR (i - 8)

def stree13RRRRLLRL (i : Nat) : State := match i with | 0 => state13_1970 | 1 => state13_1971 | 2 => state13_1972 | 3 => state13_1973 | 4 => state13_1974 | 5 => state13_1975 | 6 => state13_1976 | _ => state13_1977

def stree13RRRRLLRR (i : Nat) : State := match i with | 0 => state13_1978 | 1 => state13_1979 | 2 => state13_1980 | 3 => state13_1981 | 4 => state13_1982 | 5 => state13_1983 | 6 => state13_1984 | _ => state13_1985

def stree13RRRRLLR (i : Nat) : State := if i < 8 then stree13RRRRLLRL i else stree13RRRRLLRR (i - 8)

def stree13RRRRLL (i : Nat) : State := if i < 16 then stree13RRRRLLL i else stree13RRRRLLR (i - 16)

def stree13RRRRLRLL (i : Nat) : State := match i with | 0 => state13_1986 | 1 => state13_1987 | 2 => state13_1988 | 3 => state13_1989 | 4 => state13_1990 | 5 => state13_1991 | 6 => state13_1992 | _ => state13_1993

def stree13RRRRLRLR (i : Nat) : State := match i with | 0 => state13_1994 | 1 => state13_1995 | 2 => state13_1996 | 3 => state13_1997 | 4 => state13_1998 | 5 => state13_1999 | 6 => state13_2000 | _ => state13_2001

def stree13RRRRLRL (i : Nat) : State := if i < 8 then stree13RRRRLRLL i else stree13RRRRLRLR (i - 8)

def stree13RRRRLRRL (i : Nat) : State := match i with | 0 => state13_2002 | 1 => state13_2003 | 2 => state13_2004 | 3 => state13_2005 | 4 => state13_2006 | 5 => state13_2007 | 6 => state13_2008 | _ => state13_2009

def stree13RRRRLRRRL (i : Nat) : State := match i with | 0 => state13_2010 | 1 => state13_2011 | 2 => state13_2012 | _ => state13_2013

def stree13RRRRLRRRR (i : Nat) : State := match i with | 0 => state13_2014 | 1 => state13_2015 | 2 => state13_2016 | 3 => state13_2017 | _ => state13_2018

def stree13RRRRLRRR (i : Nat) : State := if i < 4 then stree13RRRRLRRRL i else stree13RRRRLRRRR (i - 4)

def stree13RRRRLRR (i : Nat) : State := if i < 8 then stree13RRRRLRRL i else stree13RRRRLRRR (i - 8)

def stree13RRRRLR (i : Nat) : State := if i < 16 then stree13RRRRLRL i else stree13RRRRLRR (i - 16)

def stree13RRRRL (i : Nat) : State := if i < 32 then stree13RRRRLL i else stree13RRRRLR (i - 32)

def stree13RRRRRLLL (i : Nat) : State := match i with | 0 => state13_2019 | 1 => state13_2020 | 2 => state13_2021 | 3 => state13_2022 | 4 => state13_2023 | 5 => state13_2024 | 6 => state13_2025 | _ => state13_2026

def stree13RRRRRLLR (i : Nat) : State := match i with | 0 => state13_2027 | 1 => state13_2028 | 2 => state13_2029 | 3 => state13_2030 | 4 => state13_2031 | 5 => state13_2032 | 6 => state13_2033 | _ => state13_2034

def stree13RRRRRLL (i : Nat) : State := if i < 8 then stree13RRRRRLLL i else stree13RRRRRLLR (i - 8)

def stree13RRRRRLRL (i : Nat) : State := match i with | 0 => state13_2035 | 1 => state13_2036 | 2 => state13_2037 | 3 => state13_2038 | 4 => state13_2039 | 5 => state13_2040 | 6 => state13_2041 | _ => state13_2042

def stree13RRRRRLRRL (i : Nat) : State := match i with | 0 => state13_2043 | 1 => state13_2044 | 2 => state13_2045 | _ => state13_2046

def stree13RRRRRLRRR (i : Nat) : State := match i with | 0 => state13_2047 | 1 => state13_2048 | 2 => state13_2049 | 3 => state13_2050 | _ => state13_2051

def stree13RRRRRLRR (i : Nat) : State := if i < 4 then stree13RRRRRLRRL i else stree13RRRRRLRRR (i - 4)

def stree13RRRRRLR (i : Nat) : State := if i < 8 then stree13RRRRRLRL i else stree13RRRRRLRR (i - 8)

def stree13RRRRRL (i : Nat) : State := if i < 16 then stree13RRRRRLL i else stree13RRRRRLR (i - 16)

def stree13RRRRRRLL (i : Nat) : State := match i with | 0 => state13_2052 | 1 => state13_2053 | 2 => state13_2054 | 3 => state13_2055 | 4 => state13_2056 | 5 => state13_2057 | 6 => state13_2058 | _ => state13_2059

def stree13RRRRRRLR (i : Nat) : State := match i with | 0 => state13_2060 | 1 => state13_2061 | 2 => state13_2062 | 3 => state13_2063 | 4 => state13_2064 | 5 => state13_2065 | 6 => state13_2066 | _ => state13_2067

def stree13RRRRRRL (i : Nat) : State := if i < 8 then stree13RRRRRRLL i else stree13RRRRRRLR (i - 8)

def stree13RRRRRRRL (i : Nat) : State := match i with | 0 => state13_2068 | 1 => state13_2069 | 2 => state13_2070 | 3 => state13_2071 | 4 => state13_2072 | 5 => state13_2073 | 6 => state13_2074 | _ => state13_2075

def stree13RRRRRRRRL (i : Nat) : State := match i with | 0 => state13_2076 | 1 => state13_2077 | 2 => state13_2078 | _ => state13_2079

def stree13RRRRRRRRR (i : Nat) : State := match i with | 0 => state13_2080 | 1 => state13_2081 | 2 => state13_2082 | 3 => state13_2083 | _ => state13_2084

def stree13RRRRRRRR (i : Nat) : State := if i < 4 then stree13RRRRRRRRL i else stree13RRRRRRRRR (i - 4)

def stree13RRRRRRR (i : Nat) : State := if i < 8 then stree13RRRRRRRL i else stree13RRRRRRRR (i - 8)

def stree13RRRRRR (i : Nat) : State := if i < 16 then stree13RRRRRRL i else stree13RRRRRRR (i - 16)

def stree13RRRRR (i : Nat) : State := if i < 33 then stree13RRRRRL i else stree13RRRRRR (i - 33)

def stree13RRRR (i : Nat) : State := if i < 65 then stree13RRRRL i else stree13RRRRR (i - 65)

def stree13RRR (i : Nat) : State := if i < 130 then stree13RRRL i else stree13RRRR (i - 130)

def stree13RR (i : Nat) : State := if i < 261 then stree13RRL i else stree13RRR (i - 261)

def stree13R (i : Nat) : State := if i < 521 then stree13RL i else stree13RR (i - 521)

def stree13 (i : Nat) : State := if i < 1042 then stree13L i else stree13R (i - 1042)

def ntree13LLLLLLLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | _ => ![⟨1,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩]

def ntree13LLLLLLLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | 1 => ![⟨5,by decide⟩,⟨5,by decide⟩,⟨5,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨6,by decide⟩,⟨6,by decide⟩] | 3 => ![⟨5,by decide⟩,⟨7,by decide⟩,⟨7,by decide⟩] | _ => ![⟨8,by decide⟩,⟨0,by decide⟩,⟨8,by decide⟩]

def ntree13LLLLLLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLLLLLLL i else ntree13LLLLLLLLR (i - 4)

def ntree13LLLLLLLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨9,by decide⟩,⟨1,by decide⟩,⟨9,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨2,by decide⟩,⟨10,by decide⟩] | 2 => ![⟨9,by decide⟩,⟨3,by decide⟩,⟨11,by decide⟩] | _ => ![⟨12,by decide⟩,⟨4,by decide⟩,⟨12,by decide⟩]

def ntree13LLLLLLLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨13,by decide⟩,⟨5,by decide⟩,⟨13,by decide⟩] | 1 => ![⟨12,by decide⟩,⟨6,by decide⟩,⟨14,by decide⟩] | 2 => ![⟨13,by decide⟩,⟨7,by decide⟩,⟨15,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨16,by decide⟩] | _ => ![⟨1,by decide⟩,⟨1,by decide⟩,⟨17,by decide⟩]

def ntree13LLLLLLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLLLLLRL i else ntree13LLLLLLLRR (i - 4)

def ntree13LLLLLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLLLLLLL i else ntree13LLLLLLLR (i - 9)

def ntree13LLLLLLRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨18,by decide⟩] | 1 => ![⟨5,by decide⟩,⟨5,by decide⟩,⟨19,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨20,by decide⟩,⟨0,by decide⟩] | _ => ![⟨1,by decide⟩,⟨21,by decide⟩,⟨1,by decide⟩]

def ntree13LLLLLLRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨22,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨23,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨24,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨25,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨26,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩]

def ntree13LLLLLLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLLLLRLL i else ntree13LLLLLLRLR (i - 4)

def ntree13LLLLLLRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨27,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨27,by decide⟩,⟨23,by decide⟩,⟨16,by decide⟩] | 2 => ![⟨22,by decide⟩,⟨24,by decide⟩,⟨16,by decide⟩] | 3 => ![⟨28,by decide⟩,⟨28,by decide⟩,⟨28,by decide⟩] | _ => ![⟨28,by decide⟩,⟨29,by decide⟩,⟨29,by decide⟩]

def ntree13LLLLLLRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨30,by decide⟩,⟨28,by decide⟩,⟨30,by decide⟩] | 1 => ![⟨30,by decide⟩,⟨29,by decide⟩,⟨31,by decide⟩] | 2 => ![⟨32,by decide⟩,⟨32,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨33,by decide⟩,⟨33,by decide⟩,⟨0,by decide⟩] | _ => ![⟨34,by decide⟩,⟨34,by decide⟩,⟨28,by decide⟩]

def ntree13LLLLLLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLLLLLRRL i else ntree13LLLLLLRRR (i - 5)

def ntree13LLLLLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLLLLLRL i else ntree13LLLLLLRR (i - 9)

def ntree13LLLLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 18 then ntree13LLLLLLL i else ntree13LLLLLLR (i - 18)

def ntree13LLLLLRLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨28,by decide⟩,⟨28,by decide⟩,⟨28,by decide⟩] | _ => ![⟨8,by decide⟩,⟨20,by decide⟩,⟨8,by decide⟩]

def ntree13LLLLLRLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨25,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨35,by decide⟩,⟨35,by decide⟩,⟨35,by decide⟩] | 2 => ![⟨36,by decide⟩,⟨36,by decide⟩,⟨36,by decide⟩] | 3 => ![⟨35,by decide⟩,⟨37,by decide⟩,⟨37,by decide⟩] | _ => ![⟨36,by decide⟩,⟨38,by decide⟩,⟨38,by decide⟩]

def ntree13LLLLLRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLLLRLLL i else ntree13LLLLLRLLR (i - 4)

def ntree13LLLLLRLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨39,by decide⟩,⟨39,by decide⟩,⟨39,by decide⟩] | 1 => ![⟨40,by decide⟩,⟨40,by decide⟩,⟨40,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨41,by decide⟩,⟨41,by decide⟩] | _ => ![⟨1,by decide⟩,⟨42,by decide⟩,⟨42,by decide⟩]

def ntree13LLLLLRLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨43,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨35,by decide⟩,⟨44,by decide⟩,⟨35,by decide⟩] | 2 => ![⟨45,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨46,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | _ => ![⟨47,by decide⟩,⟨35,by decide⟩,⟨35,by decide⟩]

def ntree13LLLLLRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLLLRLRL i else ntree13LLLLLRLRR (i - 4)

def ntree13LLLLLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLLLLRLL i else ntree13LLLLLRLR (i - 9)

def ntree13LLLLLRRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨48,by decide⟩,⟨48,by decide⟩,⟨48,by decide⟩] | 1 => ![⟨49,by decide⟩,⟨49,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨50,by decide⟩,⟨50,by decide⟩,⟨0,by decide⟩] | _ => ![⟨51,by decide⟩,⟨51,by decide⟩,⟨28,by decide⟩]

def ntree13LLLLLRRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨50,by decide⟩,⟨52,by decide⟩,⟨41,by decide⟩] | 1 => ![⟨53,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨54,by decide⟩,⟨35,by decide⟩,⟨54,by decide⟩] | 3 => ![⟨55,by decide⟩,⟨0,by decide⟩,⟨55,by decide⟩] | _ => ![⟨56,by decide⟩,⟨39,by decide⟩,⟨56,by decide⟩]

def ntree13LLLLLRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLLLRRLL i else ntree13LLLLLRRLR (i - 4)

def ntree13LLLLLRRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨57,by decide⟩,⟨4,by decide⟩,⟨57,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨58,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨1,by decide⟩,⟨59,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨60,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨35,by decide⟩,⟨61,by decide⟩,⟨35,by decide⟩]

def ntree13LLLLLRRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨62,by decide⟩,⟨35,by decide⟩,⟨35,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨63,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨64,by decide⟩,⟨49,by decide⟩,⟨55,by decide⟩] | 3 => ![⟨65,by decide⟩,⟨65,by decide⟩,⟨0,by decide⟩] | _ => ![⟨66,by decide⟩,⟨66,by decide⟩,⟨1,by decide⟩]

def ntree13LLLLLRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLLLLRRRL i else ntree13LLLLLRRRR (i - 5)

def ntree13LLLLLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLLLLRRL i else ntree13LLLLLRRR (i - 9)

def ntree13LLLLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 18 then ntree13LLLLLRL i else ntree13LLLLLRR (i - 18)

def ntree13LLLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 37 then ntree13LLLLLL i else ntree13LLLLLR (i - 37)

def ntree13LLLLRLLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨65,by decide⟩,⟨67,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨66,by decide⟩,⟨68,by decide⟩,⟨3,by decide⟩] | 2 => ![⟨69,by decide⟩,⟨65,by decide⟩,⟨8,by decide⟩] | _ => ![⟨69,by decide⟩,⟨67,by decide⟩,⟨10,by decide⟩]

def ntree13LLLLRLLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨70,by decide⟩,⟨70,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨70,by decide⟩,⟨71,by decide⟩,⟨2,by decide⟩] | 2 => ![⟨65,by decide⟩,⟨65,by decide⟩,⟨16,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨72,by decide⟩,⟨72,by decide⟩] | _ => ![⟨73,by decide⟩,⟨0,by decide⟩,⟨73,by decide⟩]

def ntree13LLLLRLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLLRLLLL i else ntree13LLLLRLLLR (i - 4)

def ntree13LLLLRLLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨74,by decide⟩,⟨0,by decide⟩,⟨74,by decide⟩] | 1 => ![⟨75,by decide⟩,⟨70,by decide⟩,⟨74,by decide⟩] | 2 => ![⟨74,by decide⟩,⟨72,by decide⟩,⟨76,by decide⟩] | _ => ![⟨77,by decide⟩,⟨77,by decide⟩,⟨77,by decide⟩]

def ntree13LLLLRLLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨78,by decide⟩,⟨78,by decide⟩,⟨77,by decide⟩] | 1 => ![⟨65,by decide⟩,⟨65,by decide⟩,⟨79,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨79,by decide⟩] | 3 => ![⟨80,by decide⟩,⟨77,by decide⟩,⟨80,by decide⟩] | _ => ![⟨81,by decide⟩,⟨81,by decide⟩,⟨35,by decide⟩]

def ntree13LLLLRLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLLRLLRL i else ntree13LLLLRLLRR (i - 4)

def ntree13LLLLRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLLLRLLL i else ntree13LLLLRLLR (i - 9)

def ntree13LLLLRLRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨82,by decide⟩,⟨82,by decide⟩,⟨36,by decide⟩] | 1 => ![⟨81,by decide⟩,⟨83,by decide⟩,⟨37,by decide⟩] | 2 => ![⟨82,by decide⟩,⟨84,by decide⟩,⟨38,by decide⟩] | _ => ![⟨65,by decide⟩,⟨85,by decide⟩,⟨41,by decide⟩]

def ntree13LLLLRLRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨66,by decide⟩,⟨86,by decide⟩,⟨42,by decide⟩] | 1 => ![⟨87,by decide⟩,⟨87,by decide⟩,⟨35,by decide⟩] | 2 => ![⟨87,by decide⟩,⟨88,by decide⟩,⟨37,by decide⟩] | 3 => ![⟨89,by decide⟩,⟨0,by decide⟩,⟨89,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨90,by decide⟩]

def ntree13LLLLRLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLLRLRLL i else ntree13LLLLRLRLR (i - 4)

def ntree13LLLLRLRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨91,by decide⟩,⟨81,by decide⟩,⟨54,by decide⟩] | 1 => ![⟨92,by decide⟩,⟨65,by decide⟩,⟨55,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨93,by decide⟩,⟨93,by decide⟩] | 3 => ![⟨1,by decide⟩,⟨94,by decide⟩,⟨94,by decide⟩] | _ => ![⟨95,by decide⟩,⟨0,by decide⟩,⟨95,by decide⟩]

def ntree13LLLLRLRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨96,by decide⟩,⟨96,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨93,by decide⟩,⟨97,by decide⟩] | 2 => ![⟨98,by decide⟩,⟨98,by decide⟩,⟨4,by decide⟩] | 3 => ![⟨99,by decide⟩,⟨99,by decide⟩,⟨0,by decide⟩] | _ => ![⟨100,by decide⟩,⟨98,by decide⟩,⟨12,by decide⟩]

def ntree13LLLLRLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLLLRLRRL i else ntree13LLLLRLRRR (i - 5)

def ntree13LLLLRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLLLRLRL i else ntree13LLLLRLRR (i - 9)

def ntree13LLLLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 18 then ntree13LLLLRLL i else ntree13LLLLRLR (i - 18)

def ntree13LLLLRRLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨101,by decide⟩,⟨99,by decide⟩,⟨8,by decide⟩] | 1 => ![⟨99,by decide⟩,⟨102,by decide⟩,⟨72,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨103,by decide⟩,⟨103,by decide⟩] | _ => ![⟨104,by decide⟩,⟨104,by decide⟩,⟨104,by decide⟩]

def ntree13LLLLRRLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨105,by decide⟩,⟨105,by decide⟩,⟨104,by decide⟩] | 1 => ![⟨65,by decide⟩,⟨65,by decide⟩,⟨106,by decide⟩] | 2 => ![⟨104,by decide⟩,⟨107,by decide⟩,⟨107,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨106,by decide⟩] | _ => ![⟨108,by decide⟩,⟨108,by decide⟩,⟨39,by decide⟩]

def ntree13LLLLRRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLLRRLLL i else ntree13LLLLRRLLR (i - 4)

def ntree13LLLLRRLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨109,by decide⟩,⟨109,by decide⟩,⟨35,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨110,by decide⟩,⟨110,by decide⟩] | 2 => ![⟨111,by decide⟩,⟨0,by decide⟩,⟨111,by decide⟩] | 3 => ![⟨112,by decide⟩,⟨4,by decide⟩,⟨112,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨113,by decide⟩]

def ntree13LLLLRRLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨111,by decide⟩,⟨2,by decide⟩,⟨114,by decide⟩] | 1 => ![⟨115,by decide⟩,⟨108,by decide⟩,⟨56,by decide⟩] | 2 => ![⟨116,by decide⟩,⟨98,by decide⟩,⟨57,by decide⟩] | 3 => ![⟨117,by decide⟩,⟨109,by decide⟩,⟨54,by decide⟩] | _ => ![⟨0,by decide⟩,⟨118,by decide⟩,⟨118,by decide⟩]

def ntree13LLLLRRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLLLRRLRL i else ntree13LLLLRRLRR (i - 5)

def ntree13LLLLRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLLLRRLL i else ntree13LLLLRRLR (i - 9)

def ntree13LLLLRRRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1,by decide⟩,⟨119,by decide⟩,⟨119,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨118,by decide⟩,⟨120,by decide⟩] | 2 => ![⟨9,by decide⟩,⟨119,by decide⟩,⟨121,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13LLLLRRRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨122,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨123,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨124,by decide⟩,⟨0,by decide⟩,⟨124,by decide⟩] | 3 => ![⟨125,by decide⟩,⟨1,by decide⟩,⟨125,by decide⟩] | _ => ![⟨126,by decide⟩,⟨0,by decide⟩,⟨126,by decide⟩]

def ntree13LLLLRRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLLRRRLL i else ntree13LLLLRRRLR (i - 4)

def ntree13LLLLRRRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨127,by decide⟩,⟨1,by decide⟩,⟨127,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨128,by decide⟩,⟨128,by decide⟩] | 2 => ![⟨1,by decide⟩,⟨129,by decide⟩,⟨129,by decide⟩] | 3 => ![⟨126,by decide⟩,⟨128,by decide⟩,⟨130,by decide⟩] | _ => ![⟨127,by decide⟩,⟨129,by decide⟩,⟨131,by decide⟩]

def ntree13LLLLRRRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨132,by decide⟩,⟨132,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨133,by decide⟩] | 2 => ![⟨134,by decide⟩,⟨132,by decide⟩,⟨135,by decide⟩] | 3 => ![⟨134,by decide⟩,⟨0,by decide⟩,⟨134,by decide⟩] | _ => ![⟨0,by decide⟩,⟨136,by decide⟩,⟨136,by decide⟩]

def ntree13LLLLRRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLLLRRRRL i else ntree13LLLLRRRRR (i - 5)

def ntree13LLLLRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLLLRRRL i else ntree13LLLLRRRR (i - 9)

def ntree13LLLLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 19 then ntree13LLLLRRL i else ntree13LLLLRRR (i - 19)

def ntree13LLLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 37 then ntree13LLLLRL i else ntree13LLLLRR (i - 37)

def ntree13LLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 74 then ntree13LLLLL i else ntree13LLLLR (i - 74)

def ntree13LLLRLLLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨137,by decide⟩,⟨0,by decide⟩,⟨137,by decide⟩] | 2 => ![⟨138,by decide⟩,⟨0,by decide⟩,⟨126,by decide⟩] | _ => ![⟨27,by decide⟩,⟨128,by decide⟩,⟨128,by decide⟩]

def ntree13LLLRLLLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨139,by decide⟩] | 1 => ![⟨126,by decide⟩,⟨140,by decide⟩,⟨141,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨140,by decide⟩,⟨140,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨142,by decide⟩] | _ => ![⟨8,by decide⟩,⟨132,by decide⟩,⟨143,by decide⟩]

def ntree13LLLRLLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLRLLLLL i else ntree13LLLRLLLLR (i - 4)

def ntree13LLLRLLLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨144,by decide⟩,⟨145,by decide⟩,⟨144,by decide⟩] | 1 => ![⟨144,by decide⟩,⟨146,by decide⟩,⟨147,by decide⟩] | 2 => ![⟨145,by decide⟩,⟨146,by decide⟩,⟨146,by decide⟩] | _ => ![⟨145,by decide⟩,⟨145,by decide⟩,⟨145,by decide⟩]

def ntree13LLLRLLLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨8,by decide⟩,⟨136,by decide⟩,⟨148,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨139,by decide⟩] | 2 => ![⟨126,by decide⟩,⟨0,by decide⟩,⟨126,by decide⟩] | 3 => ![⟨149,by decide⟩,⟨149,by decide⟩,⟨0,by decide⟩] | _ => ![⟨150,by decide⟩,⟨150,by decide⟩,⟨1,by decide⟩]

def ntree13LLLRLLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLRLLLRL i else ntree13LLLRLLLRR (i - 4)

def ntree13LLLRLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLLRLLLL i else ntree13LLLRLLLR (i - 9)

def ntree13LLLRLLRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨151,by decide⟩,⟨151,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨152,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨153,by decide⟩,⟨0,by decide⟩] | _ => ![⟨154,by decide⟩,⟨154,by decide⟩,⟨0,by decide⟩]

def ntree13LLLRLLRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨155,by decide⟩,⟨155,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨156,by decide⟩,⟨35,by decide⟩,⟨156,by decide⟩] | 2 => ![⟨157,by decide⟩,⟨36,by decide⟩,⟨157,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨158,by decide⟩,⟨158,by decide⟩] | _ => ![⟨126,by decide⟩,⟨158,by decide⟩,⟨159,by decide⟩]

def ntree13LLLRLLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLRLLRLL i else ntree13LLLRLLRLR (i - 4)

def ntree13LLLRLLRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨160,by decide⟩,⟨35,by decide⟩,⟨160,by decide⟩] | 1 => ![⟨35,by decide⟩,⟨161,by decide⟩,⟨161,by decide⟩] | 2 => ![⟨162,by decide⟩,⟨0,by decide⟩,⟨162,by decide⟩] | 3 => ![⟨163,by decide⟩,⟨1,by decide⟩,⟨163,by decide⟩] | _ => ![⟨164,by decide⟩,⟨0,by decide⟩,⟨164,by decide⟩]

def ntree13LLLRLLRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨22,by decide⟩,⟨158,by decide⟩,⟨158,by decide⟩] | 1 => ![⟨165,by decide⟩,⟨154,by decide⟩,⟨126,by decide⟩] | 2 => ![⟨35,by decide⟩,⟨35,by decide⟩,⟨166,by decide⟩] | 3 => ![⟨50,by decide⟩,⟨50,by decide⟩,⟨139,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13LLLRLLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLLRLLRRL i else ntree13LLLRLLRRR (i - 5)

def ntree13LLLRLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLLRLLRL i else ntree13LLLRLLRR (i - 9)

def ntree13LLLRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 18 then ntree13LLLRLLL i else ntree13LLLRLLR (i - 18)

def ntree13LLLRLRLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨167,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨168,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨169,by decide⟩,⟨0,by decide⟩,⟨169,by decide⟩] | _ => ![⟨170,by decide⟩,⟨1,by decide⟩,⟨170,by decide⟩]

def ntree13LLLRLRLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨171,by decide⟩,⟨35,by decide⟩,⟨171,by decide⟩] | 1 => ![⟨172,by decide⟩,⟨36,by decide⟩,⟨172,by decide⟩] | 2 => ![⟨169,by decide⟩,⟨128,by decide⟩,⟨173,by decide⟩] | 3 => ![⟨170,by decide⟩,⟨129,by decide⟩,⟨174,by decide⟩] | _ => ![⟨35,by decide⟩,⟨175,by decide⟩,⟨175,by decide⟩]

def ntree13LLLRLRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLRLRLLL i else ntree13LLLRLRLLR (i - 4)

def ntree13LLLRLRLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨169,by decide⟩,⟨132,by decide⟩,⟨176,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨177,by decide⟩,⟨177,by decide⟩] | 2 => ![⟨60,by decide⟩,⟨132,by decide⟩,⟨132,by decide⟩] | 3 => ![⟨178,by decide⟩,⟨0,by decide⟩,⟨178,by decide⟩] | _ => ![⟨179,by decide⟩,⟨35,by decide⟩,⟨179,by decide⟩]

def ntree13LLLRLRLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨178,by decide⟩,⟨128,by decide⟩,⟨180,by decide⟩] | 1 => ![⟨178,by decide⟩,⟨132,by decide⟩,⟨181,by decide⟩] | 2 => ![⟨54,by decide⟩,⟨175,by decide⟩,⟨182,by decide⟩] | 3 => ![⟨55,by decide⟩,⟨177,by decide⟩,⟨183,by decide⟩] | _ => ![⟨184,by decide⟩,⟨0,by decide⟩,⟨184,by decide⟩]

def ntree13LLLRLRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLLRLRLRL i else ntree13LLLRLRLRR (i - 5)

def ntree13LLLRLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLLRLRLL i else ntree13LLLRLRLR (i - 9)

def ntree13LLLRLRRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨185,by decide⟩,⟨0,by decide⟩,⟨185,by decide⟩] | 1 => ![⟨186,by decide⟩,⟨0,by decide⟩,⟨186,by decide⟩] | 2 => ![⟨187,by decide⟩,⟨188,by decide⟩,⟨187,by decide⟩] | _ => ![⟨188,by decide⟩,⟨188,by decide⟩,⟨188,by decide⟩]

def ntree13LLLRLRRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨65,by decide⟩,⟨189,by decide⟩,⟨128,by decide⟩] | 1 => ![⟨66,by decide⟩,⟨190,by decide⟩,⟨129,by decide⟩] | 2 => ![⟨65,by decide⟩,⟨191,by decide⟩,⟨132,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨192,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨193,by decide⟩,⟨132,by decide⟩]

def ntree13LLLRLRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLRLRRLL i else ntree13LLLRLRRLR (i - 4)

def ntree13LLLRLRRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨65,by decide⟩,⟨194,by decide⟩,⟨136,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨195,by decide⟩,⟨195,by decide⟩] | 2 => ![⟨70,by decide⟩,⟨196,by decide⟩,⟨128,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨197,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13LLLRLRRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨139,by decide⟩] | 1 => ![⟨65,by decide⟩,⟨65,by decide⟩,⟨142,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨192,by decide⟩,⟨8,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨193,by decide⟩,⟨143,by decide⟩] | _ => ![⟨0,by decide⟩,⟨132,by decide⟩,⟨132,by decide⟩]

def ntree13LLLRLRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLLRLRRRL i else ntree13LLLRLRRRR (i - 5)

def ntree13LLLRLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLLRLRRL i else ntree13LLLRLRRR (i - 9)

def ntree13LLLRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 19 then ntree13LLLRLRL i else ntree13LLLRLRR (i - 19)

def ntree13LLLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 37 then ntree13LLLRLL i else ntree13LLLRLR (i - 37)

def ntree13LLLRRLLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨192,by decide⟩,⟨139,by decide⟩] | 1 => ![⟨69,by decide⟩,⟨194,by decide⟩,⟨148,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨132,by decide⟩,⟨198,by decide⟩] | _ => ![⟨199,by decide⟩,⟨199,by decide⟩,⟨199,by decide⟩]

def ntree13LLLRRLLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨200,by decide⟩,⟨200,by decide⟩,⟨200,by decide⟩] | 1 => ![⟨201,by decide⟩,⟨201,by decide⟩,⟨199,by decide⟩] | 2 => ![⟨202,by decide⟩,⟨202,by decide⟩,⟨200,by decide⟩] | 3 => ![⟨203,by decide⟩,⟨203,by decide⟩,⟨203,by decide⟩] | _ => ![⟨204,by decide⟩,⟨204,by decide⟩,⟨203,by decide⟩]

def ntree13LLLRRLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLRRLLLL i else ntree13LLLRRLLLR (i - 4)

def ntree13LLLRRLLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨205,by decide⟩,⟨205,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨206,by decide⟩,⟨206,by decide⟩,⟨203,by decide⟩] | 2 => ![⟨207,by decide⟩,⟨207,by decide⟩,⟨207,by decide⟩] | _ => ![⟨0,by decide⟩,⟨208,by decide⟩,⟨0,by decide⟩]

def ntree13LLLRRLLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1,by decide⟩,⟨209,by decide⟩,⟨1,by decide⟩] | 1 => ![⟨65,by decide⟩,⟨210,by decide⟩,⟨158,by decide⟩] | 2 => ![⟨35,by decide⟩,⟨211,by decide⟩,⟨35,by decide⟩] | 3 => ![⟨81,by decide⟩,⟨212,by decide⟩,⟨161,by decide⟩] | _ => ![⟨199,by decide⟩,⟨213,by decide⟩,⟨213,by decide⟩]

def ntree13LLLRRLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLRRLLRL i else ntree13LLLRRLLRR (i - 4)

def ntree13LLLRRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLLRRLLL i else ntree13LLLRRLLR (i - 9)

def ntree13LLLRRLRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨208,by decide⟩,⟨139,by decide⟩] | 1 => ![⟨35,by decide⟩,⟨211,by decide⟩,⟨166,by decide⟩] | 2 => ![⟨203,by decide⟩,⟨203,by decide⟩,⟨214,by decide⟩] | _ => ![⟨215,by decide⟩,⟨0,by decide⟩,⟨215,by decide⟩]

def ntree13LLLRRLRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨216,by decide⟩,⟨1,by decide⟩,⟨216,by decide⟩] | 1 => ![⟨217,by decide⟩,⟨199,by decide⟩,⟨217,by decide⟩] | 2 => ![⟨218,by decide⟩,⟨200,by decide⟩,⟨218,by decide⟩] | 3 => ![⟨219,by decide⟩,⟨203,by decide⟩,⟨219,by decide⟩] | _ => ![⟨220,by decide⟩,⟨0,by decide⟩,⟨220,by decide⟩]

def ntree13LLLRRLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLRRLRLL i else ntree13LLLRRLRLR (i - 4)

def ntree13LLLRRLRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨221,by decide⟩,⟨0,by decide⟩,⟨221,by decide⟩] | 1 => ![⟨222,by decide⟩,⟨35,by decide⟩,⟨222,by decide⟩] | 2 => ![⟨223,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨224,by decide⟩,⟨203,by decide⟩,⟨224,by decide⟩] | _ => ![⟨225,by decide⟩,⟨207,by decide⟩,⟨225,by decide⟩]

def ntree13LLLRRLRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨81,by decide⟩,⟨226,by decide⟩,⟨175,by decide⟩] | 1 => ![⟨65,by decide⟩,⟨227,by decide⟩,⟨177,by decide⟩] | 2 => ![⟨199,by decide⟩,⟨228,by decide⟩,⟨228,by decide⟩] | 3 => ![⟨200,by decide⟩,⟨229,by decide⟩,⟨229,by decide⟩] | _ => ![⟨203,by decide⟩,⟨230,by decide⟩,⟨230,by decide⟩]

def ntree13LLLRRLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLLRRLRRL i else ntree13LLLRRLRRR (i - 5)

def ntree13LLLRRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLLRRLRL i else ntree13LLLRRLRR (i - 9)

def ntree13LLLRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 18 then ntree13LLLRRLL i else ntree13LLLRRLR (i - 18)

def ntree13LLLRRRLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨203,by decide⟩,⟨231,by decide⟩,⟨231,by decide⟩] | 1 => ![⟨35,by decide⟩,⟨232,by decide⟩,⟨35,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨233,by decide⟩,⟨0,by decide⟩] | _ => ![⟨221,by decide⟩,⟨93,by decide⟩,⟨234,by decide⟩]

def ntree13LLLRRRLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨219,by decide⟩,⟨230,by decide⟩,⟨235,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨236,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨237,by decide⟩] | 3 => ![⟨238,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨239,by decide⟩,⟨65,by decide⟩,⟨137,by decide⟩]

def ntree13LLLRRRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLRRRLLL i else ntree13LLLRRRLLR (i - 4)

def ntree13LLLRRRLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨240,by decide⟩,⟨0,by decide⟩,⟨126,by decide⟩] | 1 => ![⟨241,by decide⟩,⟨65,by decide⟩,⟨126,by decide⟩] | 2 => ![⟨242,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨243,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨243,by decide⟩]

def ntree13LLLRRRLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨244,by decide⟩] | 1 => ![⟨245,by decide⟩,⟨246,by decide⟩,⟨144,by decide⟩] | 2 => ![⟨246,by decide⟩,⟨246,by decide⟩,⟨145,by decide⟩] | 3 => ![⟨247,by decide⟩,⟨248,by decide⟩,⟨8,by decide⟩] | _ => ![⟨248,by decide⟩,⟨248,by decide⟩,⟨0,by decide⟩]

def ntree13LLLRRRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLLRRRLRL i else ntree13LLLRRRLRR (i - 5)

def ntree13LLLRRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLLRRRLL i else ntree13LLLRRRLR (i - 9)

def ntree13LLLRRRRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨249,by decide⟩,⟨32,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨250,by decide⟩,⟨104,by decide⟩,⟨250,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨251,by decide⟩,⟨251,by decide⟩] | _ => ![⟨0,by decide⟩,⟨252,by decide⟩,⟨252,by decide⟩]

def ntree13LLLRRRRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨253,by decide⟩,⟨253,by decide⟩] | 1 => ![⟨203,by decide⟩,⟨254,by decide⟩,⟨254,by decide⟩] | 2 => ![⟨255,by decide⟩,⟨81,by decide⟩,⟨156,by decide⟩] | 3 => ![⟨256,by decide⟩,⟨35,by decide⟩,⟨35,by decide⟩] | _ => ![⟨0,by decide⟩,⟨257,by decide⟩,⟨0,by decide⟩]

def ntree13LLLRRRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLLRRRRLL i else ntree13LLLRRRRLR (i - 4)

def ntree13LLLRRRRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨126,by decide⟩,⟨257,by decide⟩,⟨126,by decide⟩] | 1 => ![⟨258,by decide⟩,⟨65,by decide⟩,⟨162,by decide⟩] | 2 => ![⟨259,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨260,by decide⟩,⟨203,by decide⟩,⟨260,by decide⟩] | _ => ![⟨261,by decide⟩,⟨261,by decide⟩,⟨0,by decide⟩]

def ntree13LLLRRRRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨262,by decide⟩,⟨261,by decide⟩,⟨126,by decide⟩] | 1 => ![⟨263,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨264,by decide⟩,⟨65,by decide⟩,⟨178,by decide⟩] | 3 => ![⟨265,by decide⟩,⟨35,by decide⟩,⟨35,by decide⟩] | _ => ![⟨266,by decide⟩,⟨81,by decide⟩,⟨179,by decide⟩]

def ntree13LLLRRRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLLRRRRRL i else ntree13LLLRRRRRR (i - 5)

def ntree13LLLRRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLLRRRRL i else ntree13LLLRRRRR (i - 9)

def ntree13LLLRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 19 then ntree13LLLRRRL i else ntree13LLLRRRR (i - 19)

def ntree13LLLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 37 then ntree13LLLRRL i else ntree13LLLRRR (i - 37)

def ntree13LLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 75 then ntree13LLLRL i else ntree13LLLRR (i - 75)

def ntree13LLL (i : Nat) : Fin 3 → Fin 2085 := if i < 149 then ntree13LLLL i else ntree13LLLR (i - 149)

def ntree13LLRLLLLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨263,by decide⟩,⟨128,by decide⟩,⟨128,by decide⟩] | 1 => ![⟨264,by decide⟩,⟨189,by decide⟩,⟨180,by decide⟩] | 2 => ![⟨267,by decide⟩,⟨261,by decide⟩,⟨8,by decide⟩] | _ => ![⟨268,by decide⟩,⟨50,by decide⟩,⟨221,by decide⟩]

def ntree13LLRLLLLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨269,by decide⟩,⟨0,by decide⟩,⟨269,by decide⟩] | 1 => ![⟨269,by decide⟩,⟨2,by decide⟩,⟨270,by decide⟩] | 2 => ![⟨271,by decide⟩,⟨4,by decide⟩,⟨271,by decide⟩] | 3 => ![⟨271,by decide⟩,⟨6,by decide⟩,⟨272,by decide⟩] | _ => ![⟨273,by decide⟩,⟨0,by decide⟩,⟨273,by decide⟩]

def ntree13LLRLLLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRLLLLLL i else ntree13LLRLLLLLR (i - 4)

def ntree13LLRLLLLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨274,by decide⟩,⟨4,by decide⟩,⟨274,by decide⟩] | 1 => ![⟨273,by decide⟩,⟨132,by decide⟩,⟨275,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨276,by decide⟩] | _ => ![⟨4,by decide⟩,⟨277,by decide⟩,⟨277,by decide⟩]

def ntree13LLRLLLLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨274,by decide⟩,⟨277,by decide⟩,⟨278,by decide⟩] | 1 => ![⟨126,by decide⟩,⟨279,by decide⟩,⟨280,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨279,by decide⟩,⟨279,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨281,by decide⟩,⟨281,by decide⟩] | _ => ![⟨4,by decide⟩,⟨282,by decide⟩,⟨282,by decide⟩]

def ntree13LLRLLLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRLLLLRL i else ntree13LLRLLLLRR (i - 4)

def ntree13LLRLLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLRLLLLL i else ntree13LLRLLLLR (i - 9)

def ntree13LLRLLLRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨283,by decide⟩,⟨132,by decide⟩] | 1 => ![⟨273,by decide⟩,⟨23,by decide⟩,⟨273,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨284,by decide⟩] | _ => ![⟨137,by decide⟩,⟨2,by decide⟩,⟨285,by decide⟩]

def ntree13LLRLLLRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨286,by decide⟩] | 1 => ![⟨126,by decide⟩,⟨2,by decide⟩,⟨287,by decide⟩] | 2 => ![⟨288,by decide⟩,⟨289,by decide⟩,⟨289,by decide⟩] | 3 => ![⟨290,by decide⟩,⟨132,by decide⟩,⟨291,by decide⟩] | _ => ![⟨292,by decide⟩,⟨289,by decide⟩,⟨293,by decide⟩]

def ntree13LLRLLLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRLLLRLL i else ntree13LLRLLLRLR (i - 4)

def ntree13LLRLLLRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨290,by decide⟩,⟨0,by decide⟩,⟨290,by decide⟩] | 1 => ![⟨292,by decide⟩,⟨288,by decide⟩,⟨292,by decide⟩] | 2 => ![⟨288,by decide⟩,⟨288,by decide⟩,⟨288,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨286,by decide⟩] | _ => ![⟨0,by decide⟩,⟨132,by decide⟩,⟨132,by decide⟩]

def ntree13LLRLLLRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨294,by decide⟩,⟨294,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨295,by decide⟩,⟨295,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨296,by decide⟩,⟨296,by decide⟩,⟨4,by decide⟩] | 3 => ![⟨297,by decide⟩,⟨297,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨298,by decide⟩,⟨298,by decide⟩]

def ntree13LLRLLLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLRLLLRRL i else ntree13LLRLLLRRR (i - 5)

def ntree13LLRLLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLRLLLRL i else ntree13LLRLLLRR (i - 9)

def ntree13LLRLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 18 then ntree13LLRLLLL i else ntree13LLRLLLR (i - 18)

def ntree13LLRLLRLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨273,by decide⟩,⟨298,by decide⟩,⟨299,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨300,by decide⟩,⟨300,by decide⟩] | 2 => ![⟨274,by decide⟩,⟨300,by decide⟩,⟨301,by decide⟩] | _ => ![⟨126,by decide⟩,⟨298,by decide⟩,⟨302,by decide⟩]

def ntree13LLRLLRLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨273,by decide⟩,⟨158,by decide⟩,⟨303,by decide⟩] | 1 => ![⟨35,by decide⟩,⟨304,by decide⟩,⟨304,by decide⟩] | 2 => ![⟨39,by decide⟩,⟨305,by decide⟩,⟨305,by decide⟩] | 3 => ![⟨126,by decide⟩,⟨43,by decide⟩,⟨126,by decide⟩] | _ => ![⟨35,by decide⟩,⟨35,by decide⟩,⟨306,by decide⟩]

def ntree13LLRLLRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRLLRLLL i else ntree13LLRLLRLLR (i - 4)

def ntree13LLRLLRLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨156,by decide⟩,⟨37,by decide⟩,⟨307,by decide⟩] | 1 => ![⟨162,by decide⟩,⟨41,by decide⟩,⟨308,by decide⟩] | 2 => ![⟨49,by decide⟩,⟨49,by decide⟩,⟨286,by decide⟩] | 3 => ![⟨309,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨310,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13LLRLLRLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨39,by decide⟩,⟨311,by decide⟩,⟨311,by decide⟩] | 1 => ![⟨35,by decide⟩,⟨312,by decide⟩,⟨312,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨313,by decide⟩,⟨313,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨314,by decide⟩,⟨314,by decide⟩] | _ => ![⟨295,by decide⟩,⟨315,by decide⟩,⟨132,by decide⟩]

def ntree13LLRLLRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLRLLRLRL i else ntree13LLRLLRLRR (i - 5)

def ntree13LLRLLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLRLLRLL i else ntree13LLRLLRLR (i - 9)

def ntree13LLRLLRRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨178,by decide⟩,⟨24,by decide⟩,⟨178,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨316,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨317,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13LLRLLRRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨318,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨319,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨320,by decide⟩,⟨320,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨321,by decide⟩,⟨321,by decide⟩] | _ => ![⟨0,by decide⟩,⟨322,by decide⟩,⟨322,by decide⟩]

def ntree13LLRLLRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRLLRRLL i else ntree13LLRLLRRLR (i - 4)

def ntree13LLRLLRRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨188,by decide⟩,⟨323,by decide⟩,⟨323,by decide⟩] | 1 => ![⟨324,by decide⟩,⟨65,by decide⟩,⟨273,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨325,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨325,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨326,by decide⟩]

def ntree13LLRLLRRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨327,by decide⟩,⟨0,by decide⟩,⟨327,by decide⟩] | 1 => ![⟨328,by decide⟩,⟨329,by decide⟩,⟨289,by decide⟩] | 2 => ![⟨328,by decide⟩,⟨328,by decide⟩,⟨288,by decide⟩] | 3 => ![⟨77,by decide⟩,⟨330,by decide⟩,⟨330,by decide⟩] | _ => ![⟨331,by decide⟩,⟨332,by decide⟩,⟨2,by decide⟩]

def ntree13LLRLLRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLRLLRRRL i else ntree13LLRLLRRRR (i - 5)

def ntree13LLRLLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLRLLRRL i else ntree13LLRLLRRR (i - 9)

def ntree13LLRLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 19 then ntree13LLRLLRL i else ntree13LLRLLRR (i - 19)

def ntree13LLRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 37 then ntree13LLRLLL i else ntree13LLRLLR (i - 37)

def ntree13LLRLRLLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨331,by decide⟩,⟨331,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨33,by decide⟩,⟨333,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨334,by decide⟩,⟨334,by decide⟩] | _ => ![⟨203,by decide⟩,⟨335,by decide⟩,⟨335,by decide⟩]

def ntree13LLRLRLLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨336,by decide⟩,⟨336,by decide⟩] | 1 => ![⟨203,by decide⟩,⟨337,by decide⟩,⟨337,by decide⟩] | 2 => ![⟨35,by decide⟩,⟨338,by decide⟩,⟨338,by decide⟩] | 3 => ![⟨207,by decide⟩,⟨339,by decide⟩,⟨339,by decide⟩] | _ => ![⟨273,by decide⟩,⟨208,by decide⟩,⟨273,by decide⟩]

def ntree13LLRLRLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRLRLLLL i else ntree13LLRLRLLLR (i - 4)

def ntree13LLRLRLLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨324,by decide⟩,⟨210,by decide⟩,⟨303,by decide⟩] | 1 => ![⟨340,by decide⟩,⟨203,by decide⟩,⟨340,by decide⟩] | 2 => ![⟨341,by decide⟩,⟨342,by decide⟩,⟨2,by decide⟩] | _ => ![⟨49,by decide⟩,⟨343,by decide⟩,⟨336,by decide⟩]

def ntree13LLRLRLLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨344,by decide⟩,⟨0,by decide⟩,⟨344,by decide⟩] | 1 => ![⟨345,by decide⟩,⟨0,by decide⟩,⟨345,by decide⟩] | 2 => ![⟨346,by decide⟩,⟨0,by decide⟩,⟨346,by decide⟩] | 3 => ![⟨347,by decide⟩,⟨203,by decide⟩,⟨347,by decide⟩] | _ => ![⟨348,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13LLRLRLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRLRLLRL i else ntree13LLRLRLLRR (i - 4)

def ntree13LLRLRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLRLRLLL i else ntree13LLRLRLLR (i - 9)

def ntree13LLRLRLRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨348,by decide⟩,⟨132,by decide⟩,⟨132,by decide⟩] | 1 => ![⟨341,by decide⟩,⟨341,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨341,by decide⟩,⟨349,by decide⟩,⟨132,by decide⟩] | _ => ![⟨350,by decide⟩,⟨98,by decide⟩,⟨274,by decide⟩]

def ntree13LLRLRLRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨351,by decide⟩,⟨99,by decide⟩,⟨273,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨65,by decide⟩,⟨65,by decide⟩,⟨284,by decide⟩] | 3 => ![⟨238,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | _ => ![⟨239,by decide⟩,⟨67,by decide⟩,⟨285,by decide⟩]

def ntree13LLRLRLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRLRLRLL i else ntree13LLRLRLRLR (i - 4)

def ntree13LLRLRLRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨286,by decide⟩] | 1 => ![⟨240,by decide⟩,⟨2,by decide⟩,⟨287,by decide⟩] | 2 => ![⟨126,by decide⟩,⟨0,by decide⟩,⟨126,by decide⟩] | 3 => ![⟨238,by decide⟩,⟨0,by decide⟩,⟨286,by decide⟩] | _ => ![⟨126,by decide⟩,⟨0,by decide⟩,⟨352,by decide⟩]

def ntree13LLRLRLRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨353,by decide⟩,⟨353,by decide⟩,⟨353,by decide⟩] | 1 => ![⟨354,by decide⟩,⟨354,by decide⟩,⟨353,by decide⟩] | 2 => ![⟨355,by decide⟩,⟨355,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨356,by decide⟩,⟨356,by decide⟩,⟨356,by decide⟩] | _ => ![⟨357,by decide⟩,⟨357,by decide⟩,⟨356,by decide⟩]

def ntree13LLRLRLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLRLRLRRL i else ntree13LLRLRLRRR (i - 5)

def ntree13LLRLRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLRLRLRL i else ntree13LLRLRLRR (i - 9)

def ntree13LLRLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 18 then ntree13LLRLRLL i else ntree13LLRLRLR (i - 18)

def ntree13LLRLRRLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨358,by decide⟩,⟨358,by decide⟩,⟨203,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨359,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨360,by decide⟩,⟨360,by decide⟩] | _ => ![⟨353,by decide⟩,⟨361,by decide⟩,⟨361,by decide⟩]

def ntree13LLRLRRLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨4,by decide⟩,⟨362,by decide⟩,⟨362,by decide⟩] | 1 => ![⟨356,by decide⟩,⟨363,by decide⟩,⟨363,by decide⟩] | 2 => ![⟨364,by decide⟩,⟨353,by decide⟩,⟨364,by decide⟩] | 3 => ![⟨365,by decide⟩,⟨356,by decide⟩,⟨365,by decide⟩] | _ => ![⟨203,by decide⟩,⟨203,by decide⟩,⟨366,by decide⟩]

def ntree13LLRLRRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRLRRLLL i else ntree13LLRLRRLLR (i - 4)

def ntree13LLRLRRLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨111,by decide⟩,⟨336,by decide⟩,⟨367,by decide⟩] | 1 => ![⟨260,by decide⟩,⟨337,by decide⟩,⟨368,by decide⟩] | 2 => ![⟨369,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | 3 => ![⟨370,by decide⟩,⟨353,by decide⟩,⟨370,by decide⟩] | _ => ![⟨263,by decide⟩,⟨0,by decide⟩,⟨286,by decide⟩]

def ntree13LLRLRRLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨265,by decide⟩,⟨35,by decide⟩,⟨306,by decide⟩] | 1 => ![⟨371,by decide⟩,⟨371,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨372,by decide⟩,⟨372,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨373,by decide⟩,⟨373,by decide⟩,⟨4,by decide⟩] | _ => ![⟨374,by decide⟩,⟨374,by decide⟩,⟨5,by decide⟩]

def ntree13LLRLRRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLRLRRLRL i else ntree13LLRLRRLRR (i - 5)

def ntree13LLRLRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLRLRRLL i else ntree13LLRLRRLR (i - 9)

def ntree13LLRLRRRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨375,by decide⟩,⟨375,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨376,by decide⟩,⟨376,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨377,by decide⟩,⟨378,by decide⟩,⟨8,by decide⟩] | _ => ![⟨379,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13LLRLRRRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨380,by decide⟩,⟨381,by decide⟩,⟨12,by decide⟩] | 1 => ![⟨382,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | 2 => ![⟨383,by decide⟩,⟨384,by decide⟩,⟨8,by decide⟩] | 3 => ![⟨385,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨378,by decide⟩,⟨378,by decide⟩,⟨0,by decide⟩]

def ntree13LLRLRRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRLRRRLL i else ntree13LLRLRRRLR (i - 4)

def ntree13LLRLRRRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨386,by decide⟩,⟨386,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨381,by decide⟩,⟨381,by decide⟩,⟨4,by decide⟩] | 2 => ![⟨384,by decide⟩,⟨384,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨387,by decide⟩,⟨386,by decide⟩,⟨8,by decide⟩] | _ => ![⟨0,by decide⟩,⟨388,by decide⟩,⟨388,by decide⟩]

def ntree13LLRLRRRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1,by decide⟩,⟨389,by decide⟩,⟨389,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨390,by decide⟩,⟨390,by decide⟩] | 2 => ![⟨5,by decide⟩,⟨391,by decide⟩,⟨391,by decide⟩] | 3 => ![⟨375,by decide⟩,⟨392,by decide⟩,⟨388,by decide⟩] | _ => ![⟨376,by decide⟩,⟨393,by decide⟩,⟨389,by decide⟩]

def ntree13LLRLRRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLRLRRRRL i else ntree13LLRLRRRRR (i - 5)

def ntree13LLRLRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLRLRRRL i else ntree13LLRLRRRR (i - 9)

def ntree13LLRLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 19 then ntree13LLRLRRL i else ntree13LLRLRRR (i - 19)

def ntree13LLRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 37 then ntree13LLRLRL i else ntree13LLRLRR (i - 37)

def ntree13LLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 75 then ntree13LLRLL i else ntree13LLRLR (i - 75)

def ntree13LLRRLLLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨384,by decide⟩,⟨394,by decide⟩,⟨388,by decide⟩] | 1 => ![⟨386,by decide⟩,⟨395,by decide⟩,⟨388,by decide⟩] | 2 => ![⟨28,by decide⟩,⟨396,by decide⟩,⟨396,by decide⟩] | _ => ![⟨8,by decide⟩,⟨388,by decide⟩,⟨397,by decide⟩]

def ntree13LLRRLLLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨398,by decide⟩,⟨398,by decide⟩,⟨28,by decide⟩] | 1 => ![⟨379,by decide⟩,⟨388,by decide⟩,⟨388,by decide⟩] | 2 => ![⟨399,by decide⟩,⟨399,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨400,by decide⟩,⟨400,by decide⟩,⟨1,by decide⟩] | _ => ![⟨401,by decide⟩,⟨401,by decide⟩,⟨4,by decide⟩]

def ntree13LLRRLLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRRLLLLL i else ntree13LLRRLLLLR (i - 4)

def ntree13LLRRLLLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨402,by decide⟩,⟨402,by decide⟩,⟨5,by decide⟩] | 1 => ![⟨403,by decide⟩,⟨399,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨404,by decide⟩,⟨404,by decide⟩,⟨35,by decide⟩] | _ => ![⟨405,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13LLRRLLLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨406,by decide⟩,⟨35,by decide⟩,⟨35,by decide⟩] | 1 => ![⟨399,by decide⟩,⟨407,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨408,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨409,by decide⟩] | _ => ![⟨28,by decide⟩,⟨28,by decide⟩,⟨410,by decide⟩]

def ntree13LLRRLLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRRLLLRL i else ntree13LLRRLLLRR (i - 4)

def ntree13LLRRLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLRRLLLL i else ntree13LLRRLLLR (i - 9)

def ntree13LLRRLLRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨411,by decide⟩] | 1 => ![⟨35,by decide⟩,⟨35,by decide⟩,⟨412,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨413,by decide⟩] | _ => ![⟨414,by decide⟩,⟨414,by decide⟩,⟨0,by decide⟩]

def ntree13LLRRLLRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨415,by decide⟩,⟨415,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨416,by decide⟩,⟨416,by decide⟩,⟨28,by decide⟩] | 2 => ![⟨417,by decide⟩,⟨399,by decide⟩,⟨8,by decide⟩] | 3 => ![⟨418,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨419,by decide⟩,⟨401,by decide⟩,⟨12,by decide⟩]

def ntree13LLRRLLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRRLLRLL i else ntree13LLRRLLRLR (i - 4)

def ntree13LLRRLLRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨420,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | 1 => ![⟨421,by decide⟩,⟨404,by decide⟩,⟨54,by decide⟩] | 2 => ![⟨422,by decide⟩,⟨386,by decide⟩,⟨55,by decide⟩] | 3 => ![⟨35,by decide⟩,⟨423,by decide⟩,⟨423,by decide⟩] | _ => ![⟨36,by decide⟩,⟨424,by decide⟩,⟨424,by decide⟩]

def ntree13LLRRLLRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨425,by decide⟩,⟨425,by decide⟩] | 1 => ![⟨1,by decide⟩,⟨426,by decide⟩,⟨426,by decide⟩] | 2 => ![⟨399,by decide⟩,⟨427,by decide⟩,⟨388,by decide⟩] | 3 => ![⟨400,by decide⟩,⟨428,by decide⟩,⟨389,by decide⟩] | _ => ![⟨404,by decide⟩,⟨429,by decide⟩,⟨423,by decide⟩]

def ntree13LLRRLLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLRRLLRRL i else ntree13LLRRLLRRR (i - 5)

def ntree13LLRRLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLRRLLRL i else ntree13LLRRLLRR (i - 9)

def ntree13LLRRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 18 then ntree13LLRRLLL i else ntree13LLRRLLR (i - 18)

def ntree13LLRRLRLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨386,by decide⟩,⟨430,by decide⟩,⟨425,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨431,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨425,by decide⟩,⟨432,by decide⟩] | _ => ![⟨28,by decide⟩,⟨28,by decide⟩,⟨433,by decide⟩]

def ntree13LLRRLRLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨55,by decide⟩,⟨388,by decide⟩,⟨434,by decide⟩] | 1 => ![⟨54,by decide⟩,⟨423,by decide⟩,⟨435,by decide⟩] | 2 => ![⟨414,by decide⟩,⟨436,by decide⟩,⟨388,by decide⟩] | 3 => ![⟨437,by decide⟩,⟨415,by decide⟩,⟨8,by decide⟩] | _ => ![⟨438,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13LLRRLRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRRLRLLL i else ntree13LLRRLRLLR (i - 4)

def ntree13LLRRLRLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨439,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨1,by decide⟩,⟨440,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨439,by decide⟩,⟨8,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨441,by decide⟩,⟨441,by decide⟩] | _ => ![⟨1,by decide⟩,⟨442,by decide⟩,⟨442,by decide⟩]

def ntree13LLRRLRLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨375,by decide⟩,⟨443,by decide⟩,⟨441,by decide⟩] | 1 => ![⟨376,by decide⟩,⟨444,by decide⟩,⟨442,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨441,by decide⟩,⟨445,by decide⟩] | 3 => ![⟨9,by decide⟩,⟨442,by decide⟩,⟨446,by decide⟩] | _ => ![⟨383,by decide⟩,⟨447,by decide⟩,⟨445,by decide⟩]

def ntree13LLRRLRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLRRLRLRL i else ntree13LLRRLRLRR (i - 5)

def ntree13LLRRLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLRRLRLL i else ntree13LLRRLRLR (i - 9)

def ntree13LLRRLRRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨385,by decide⟩,⟨441,by decide⟩,⟨441,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨448,by decide⟩,⟨448,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨449,by decide⟩,⟨0,by decide⟩] | _ => ![⟨386,by decide⟩,⟨450,by decide⟩,⟨448,by decide⟩]

def ntree13LLRRLRRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨451,by decide⟩,⟨451,by decide⟩] | 1 => ![⟨386,by decide⟩,⟨452,by decide⟩,⟨451,by decide⟩] | 2 => ![⟨384,by decide⟩,⟨453,by decide⟩,⟨448,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨448,by decide⟩,⟨454,by decide⟩] | _ => ![⟨0,by decide⟩,⟨455,by decide⟩,⟨455,by decide⟩]

def ntree13LLRRLRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRRLRRLL i else ntree13LLRRLRRLR (i - 4)

def ntree13LLRRLRRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1,by decide⟩,⟨456,by decide⟩,⟨456,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨457,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨458,by decide⟩] | _ => ![⟨1,by decide⟩,⟨1,by decide⟩,⟨459,by decide⟩]

def ntree13LLRRLRRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨384,by decide⟩,⟨384,by decide⟩,⟨458,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨460,by decide⟩] | 2 => ![⟨461,by decide⟩,⟨462,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨461,by decide⟩,⟨461,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨463,by decide⟩,⟨463,by decide⟩]

def ntree13LLRRLRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLRRLRRRL i else ntree13LLRRLRRRR (i - 5)

def ntree13LLRRLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLRRLRRL i else ntree13LLRRLRRR (i - 9)

def ntree13LLRRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 19 then ntree13LLRRLRL i else ntree13LLRRLRR (i - 19)

def ntree13LLRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 37 then ntree13LLRRLL i else ntree13LLRRLR (i - 37)

def ntree13LLRRRLLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨375,by decide⟩,⟨464,by decide⟩,⟨448,by decide⟩] | 1 => ![⟨77,by decide⟩,⟨465,by decide⟩,⟨465,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨466,by decide⟩,⟨0,by decide⟩] | _ => ![⟨35,by decide⟩,⟨467,by decide⟩,⟨35,by decide⟩]

def ntree13LLRRRLLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨36,by decide⟩,⟨468,by decide⟩,⟨36,by decide⟩] | 1 => ![⟨399,by decide⟩,⟨469,by decide⟩,⟨441,by decide⟩] | 2 => ![⟨400,by decide⟩,⟨470,by decide⟩,⟨442,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨471,by decide⟩] | _ => ![⟨1,by decide⟩,⟨1,by decide⟩,⟨472,by decide⟩]

def ntree13LLRRRLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRRRLLLL i else ntree13LLRRRLLLR (i - 4)

def ntree13LLRRRLLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨473,by decide⟩] | 1 => ![⟨399,by decide⟩,⟨399,by decide⟩,⟨473,by decide⟩] | 2 => ![⟨35,by decide⟩,⟨474,by decide⟩,⟨474,by decide⟩] | _ => ![⟨0,by decide⟩,⟨475,by decide⟩,⟨475,by decide⟩]

def ntree13LLRRRLLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨399,by decide⟩,⟨476,by decide⟩,⟨475,by decide⟩] | 1 => ![⟨404,by decide⟩,⟨477,by decide⟩,⟨474,by decide⟩] | 2 => ![⟨386,by decide⟩,⟨386,by decide⟩,⟨471,by decide⟩] | 3 => ![⟨405,by decide⟩,⟨448,by decide⟩,⟨448,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨478,by decide⟩]

def ntree13LLRRRLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRRRLLRL i else ntree13LLRRRLLRR (i - 4)

def ntree13LLRRRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLRRRLLL i else ntree13LLRRRLLR (i - 9)

def ntree13LLRRRLRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨479,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨414,by decide⟩,⟨480,by decide⟩,⟨448,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨481,by decide⟩,⟨481,by decide⟩] | _ => ![⟨399,by decide⟩,⟨482,by decide⟩,⟨481,by decide⟩]

def ntree13LLRRRLRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨8,by decide⟩,⟨481,by decide⟩,⟨483,by decide⟩] | 1 => ![⟨35,by decide⟩,⟨484,by decide⟩,⟨484,by decide⟩] | 2 => ![⟨399,by decide⟩,⟨485,by decide⟩,⟨451,by decide⟩] | 3 => ![⟨404,by decide⟩,⟨486,by decide⟩,⟨484,by decide⟩] | _ => ![⟨386,by decide⟩,⟨487,by decide⟩,⟨481,by decide⟩]

def ntree13LLRRRLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRRRLRLL i else ntree13LLRRRLRLR (i - 4)

def ntree13LLRRRLRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨387,by decide⟩,⟨487,by decide⟩,⟨483,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨488,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨489,by decide⟩,⟨489,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨490,by decide⟩,⟨490,by decide⟩] | _ => ![⟨12,by decide⟩,⟨489,by decide⟩,⟨491,by decide⟩]

def ntree13LLRRRLRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨8,by decide⟩,⟨490,by decide⟩,⟨492,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨493,by decide⟩,⟨493,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨494,by decide⟩,⟨494,by decide⟩] | 3 => ![⟨457,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨495,by decide⟩]

def ntree13LLRRRLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLRRRLRRL i else ntree13LLRRRLRRR (i - 5)

def ntree13LLRRRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLRRRLRL i else ntree13LLRRRLRR (i - 9)

def ntree13LLRRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 18 then ntree13LLRRRLL i else ntree13LLRRRLR (i - 18)

def ntree13LLRRRRLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨496,by decide⟩] | 1 => ![⟨497,by decide⟩,⟨498,by decide⟩,⟨388,by decide⟩] | 2 => ![⟨499,by decide⟩,⟨500,by decide⟩,⟨0,by decide⟩] | _ => ![⟨104,by decide⟩,⟨501,by decide⟩,⟨501,by decide⟩]

def ntree13LLRRRRLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨448,by decide⟩,⟨448,by decide⟩] | 1 => ![⟨502,by decide⟩,⟨502,by decide⟩,⟨4,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨503,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨448,by decide⟩,⟨504,by decide⟩] | _ => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨505,by decide⟩]

def ntree13LLRRRRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRRRRLLL i else ntree13LLRRRRLLR (i - 4)

def ntree13LLRRRRLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨39,by decide⟩,⟨506,by decide⟩,⟨506,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨507,by decide⟩,⟨507,by decide⟩] | 2 => ![⟨35,by decide⟩,⟨508,by decide⟩,⟨508,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨509,by decide⟩,⟨509,by decide⟩] | _ => ![⟨510,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13LLRRRRLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨510,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨511,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨510,by decide⟩,⟨439,by decide⟩,⟨408,by decide⟩] | 3 => ![⟨512,by decide⟩,⟨439,by decide⟩,⟨411,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13LLRRRRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLRRRRLRL i else ntree13LLRRRRLRR (i - 5)

def ntree13LLRRRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLRRRRLL i else ntree13LLRRRRLR (i - 9)

def ntree13LLRRRRRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨513,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨111,by decide⟩,⟨448,by decide⟩,⟨514,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨515,by decide⟩,⟨515,by decide⟩] | _ => ![⟨4,by decide⟩,⟨516,by decide⟩,⟨516,by decide⟩]

def ntree13LLRRRRRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨8,by decide⟩,⟨515,by decide⟩,⟨517,by decide⟩] | 1 => ![⟨12,by decide⟩,⟨516,by decide⟩,⟨518,by decide⟩] | 2 => ![⟨35,by decide⟩,⟨519,by decide⟩,⟨519,by decide⟩] | 3 => ![⟨39,by decide⟩,⟨520,by decide⟩,⟨520,by decide⟩] | _ => ![⟨74,by decide⟩,⟨425,by decide⟩,⟨521,by decide⟩]

def ntree13LLRRRRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LLRRRRRLL i else ntree13LLRRRRRLR (i - 4)

def ntree13LLRRRRRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨522,by decide⟩] | 1 => ![⟨1,by decide⟩,⟨1,by decide⟩,⟨523,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨524,by decide⟩,⟨524,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨525,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13LLRRRRRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨526,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨126,by decide⟩,⟨388,by decide⟩,⟨527,by decide⟩] | 2 => ![⟨127,by decide⟩,⟨389,by decide⟩,⟨528,by decide⟩] | 3 => ![⟨134,by decide⟩,⟨388,by decide⟩,⟨529,by decide⟩] | _ => ![⟨530,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13LLRRRRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LLRRRRRRL i else ntree13LLRRRRRRR (i - 5)

def ntree13LLRRRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LLRRRRRL i else ntree13LLRRRRRR (i - 9)

def ntree13LLRRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 19 then ntree13LLRRRRL i else ntree13LLRRRRR (i - 19)

def ntree13LLRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 37 then ntree13LLRRRL i else ntree13LLRRRR (i - 37)

def ntree13LLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 75 then ntree13LLRRL i else ntree13LLRRR (i - 75)

def ntree13LLR (i : Nat) : Fin 3 → Fin 2085 := if i < 150 then ntree13LLRL i else ntree13LLRR (i - 150)

def ntree13LL (i : Nat) : Fin 3 → Fin 2085 := if i < 299 then ntree13LLL i else ntree13LLR (i - 299)

def ntree13LRLLLLLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨530,by decide⟩,⟨388,by decide⟩,⟨388,by decide⟩] | 1 => ![⟨531,by decide⟩,⟨378,by decide⟩,⟨126,by decide⟩] | 2 => ![⟨532,by decide⟩,⟨533,by decide⟩,⟨8,by decide⟩] | _ => ![⟨534,by decide⟩,⟨535,by decide⟩,⟨0,by decide⟩]

def ntree13LRLLLLLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨536,by decide⟩] | 1 => ![⟨1,by decide⟩,⟨1,by decide⟩,⟨537,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨538,by decide⟩,⟨538,by decide⟩] | 3 => ![⟨1,by decide⟩,⟨539,by decide⟩,⟨539,by decide⟩] | _ => ![⟨0,by decide⟩,⟨540,by decide⟩,⟨540,by decide⟩]

def ntree13LRLLLLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLLLLLLL i else ntree13LRLLLLLLR (i - 4)

def ntree13LRLLLLLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨541,by decide⟩,⟨541,by decide⟩,⟨1,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨542,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨543,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨543,by decide⟩,⟨0,by decide⟩]

def ntree13LRLLLLLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨126,by decide⟩,⟨0,by decide⟩,⟨544,by decide⟩] | 1 => ![⟨545,by decide⟩,⟨35,by decide⟩,⟨35,by decide⟩] | 2 => ![⟨546,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨547,by decide⟩,⟨415,by decide⟩,⟨126,by decide⟩] | _ => ![⟨126,by decide⟩,⟨538,by decide⟩,⟨548,by decide⟩]

def ntree13LRLLLLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLLLLLRL i else ntree13LRLLLLLRR (i - 4)

def ntree13LRLLLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LRLLLLLL i else ntree13LRLLLLLR (i - 9)

def ntree13LRLLLLRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨530,by decide⟩,⟨543,by decide⟩,⟨408,by decide⟩] | 1 => ![⟨530,by decide⟩,⟨549,by decide⟩,⟨409,by decide⟩] | 2 => ![⟨55,by decide⟩,⟨524,by decide⟩,⟨550,by decide⟩] | _ => ![⟨169,by decide⟩,⟨388,by decide⟩,⟨551,by decide⟩]

def ntree13LRLLLLRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨170,by decide⟩,⟨389,by decide⟩,⟨552,by decide⟩] | 1 => ![⟨178,by decide⟩,⟨388,by decide⟩,⟨553,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨554,by decide⟩,⟨554,by decide⟩] | 3 => ![⟨184,by decide⟩,⟨448,by decide⟩,⟨555,by decide⟩] | _ => ![⟨0,by decide⟩,⟨556,by decide⟩,⟨0,by decide⟩]

def ntree13LRLLLLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLLLLRLL i else ntree13LRLLLLRLR (i - 4)

def ntree13LRLLLLRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨1,by decide⟩,⟨557,by decide⟩,⟨1,by decide⟩] | 1 => ![⟨530,by decide⟩,⟨556,by decide⟩,⟨458,by decide⟩] | 2 => ![⟨534,by decide⟩,⟨558,by decide⟩,⟨448,by decide⟩] | 3 => ![⟨530,by decide⟩,⟨451,by decide⟩,⟨451,by decide⟩] | _ => ![⟨0,by decide⟩,⟨448,by decide⟩,⟨448,by decide⟩]

def ntree13LRLLLLRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨199,by decide⟩,⟨559,by decide⟩,⟨559,by decide⟩] | 1 => ![⟨200,by decide⟩,⟨560,by decide⟩,⟨560,by decide⟩] | 2 => ![⟨203,by decide⟩,⟨561,by decide⟩,⟨561,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨448,by decide⟩,⟨562,by decide⟩] | _ => ![⟨203,by decide⟩,⟨563,by decide⟩,⟨563,by decide⟩]

def ntree13LRLLLLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LRLLLLRRL i else ntree13LRLLLLRRR (i - 5)

def ntree13LRLLLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LRLLLLRL i else ntree13LRLLLLRR (i - 9)

def ntree13LRLLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 18 then ntree13LRLLLLL i else ntree13LRLLLLR (i - 18)

def ntree13LRLLLRLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨564,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨530,by decide⟩,⟨208,by decide⟩,⟨471,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨565,by decide⟩,⟨448,by decide⟩] | _ => ![⟨199,by decide⟩,⟨566,by decide⟩,⟨566,by decide⟩]

def ntree13LRLLLRLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨567,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨568,by decide⟩,⟨568,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨126,by decide⟩,⟨569,by decide⟩,⟨570,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨569,by decide⟩,⟨569,by decide⟩] | _ => ![⟨0,by decide⟩,⟨571,by decide⟩,⟨571,by decide⟩]

def ntree13LRLLLRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLLLRLLL i else ntree13LRLLLRLLR (i - 4)

def ntree13LRLLLRLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨572,by decide⟩,⟨572,by decide⟩] | 1 => ![⟨188,by decide⟩,⟨573,by decide⟩,⟨573,by decide⟩] | 2 => ![⟨137,by decide⟩,⟨448,by decide⟩,⟨574,by decide⟩] | _ => ![⟨126,by decide⟩,⟨451,by decide⟩,⟨575,by decide⟩]

def ntree13LRLLLRLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨126,by decide⟩,⟨448,by decide⟩,⟨576,by decide⟩] | 1 => ![⟨250,by decide⟩,⟨501,by decide⟩,⟨577,by decide⟩] | 2 => ![⟨185,by decide⟩,⟨388,by decide⟩,⟨578,by decide⟩] | 3 => ![⟨144,by decide⟩,⟨579,by decide⟩,⟨580,by decide⟩] | _ => ![⟨145,by decide⟩,⟨579,by decide⟩,⟨579,by decide⟩]

def ntree13LRLLLRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLLLRLRL i else ntree13LRLLLRLRR (i - 4)

def ntree13LRLLLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LRLLLRLL i else ntree13LRLLLRLR (i - 9)

def ntree13LRLLLRRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨126,by decide⟩,⟨448,by decide⟩,⟨581,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨571,by decide⟩,⟨582,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨572,by decide⟩,⟨583,by decide⟩] | _ => ![⟨186,by decide⟩,⟨388,by decide⟩,⟨584,by decide⟩]

def ntree13LRLLLRRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨187,by decide⟩,⟨573,by decide⟩,⟨585,by decide⟩] | 1 => ![⟨586,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨587,by decide⟩,⟨587,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨588,by decide⟩,⟨588,by decide⟩,⟨0,by decide⟩] | _ => ![⟨586,by decide⟩,⟨448,by decide⟩,⟨448,by decide⟩]

def ntree13LRLLLRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLLLRRLL i else ntree13LRLLLRRLR (i - 4)

def ntree13LRLLLRRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨126,by decide⟩,⟨0,by decide⟩,⟨589,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨590,by decide⟩] | 2 => ![⟨162,by decide⟩,⟨448,by decide⟩,⟨591,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨592,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨593,by decide⟩]

def ntree13LRLLLRRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨203,by decide⟩,⟨203,by decide⟩,⟨594,by decide⟩] | 1 => ![⟨126,by decide⟩,⟨475,by decide⟩,⟨595,by decide⟩] | 2 => ![⟨156,by decide⟩,⟨474,by decide⟩,⟨596,by decide⟩] | 3 => ![⟨126,by decide⟩,⟨448,by decide⟩,⟨597,by decide⟩] | _ => ![⟨35,by decide⟩,⟨35,by decide⟩,⟨598,by decide⟩]

def ntree13LRLLLRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LRLLLRRRL i else ntree13LRLLLRRRR (i - 5)

def ntree13LRLLLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LRLLLRRL i else ntree13LRLLLRRR (i - 9)

def ntree13LRLLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 18 then ntree13LRLLLRL i else ntree13LRLLLRR (i - 18)

def ntree13LRLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 37 then ntree13LRLLLL i else ntree13LRLLLR (i - 37)

def ntree13LRLLRLLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨126,by decide⟩,⟨448,by decide⟩,⟨599,by decide⟩] | 1 => ![⟨260,by decide⟩,⟨563,by decide⟩,⟨600,by decide⟩] | 2 => ![⟨203,by decide⟩,⟨203,by decide⟩,⟨601,by decide⟩] | _ => ![⟨35,by decide⟩,⟨35,by decide⟩,⟨602,by decide⟩]

def ntree13LRLLRLLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨203,by decide⟩,⟨203,by decide⟩,⟨603,by decide⟩] | 1 => ![⟨207,by decide⟩,⟨207,by decide⟩,⟨604,by decide⟩] | 2 => ![⟨567,by decide⟩,⟨481,by decide⟩,⟨481,by decide⟩] | 3 => ![⟨178,by decide⟩,⟨556,by decide⟩,⟨178,by decide⟩] | _ => ![⟨0,by decide⟩,⟨605,by decide⟩,⟨605,by decide⟩]

def ntree13LRLLRLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLLRLLLL i else ntree13LRLLRLLLR (i - 4)

def ntree13LRLLRLLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨203,by decide⟩,⟨606,by decide⟩,⟨606,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨607,by decide⟩,⟨607,by decide⟩] | 2 => ![⟨203,by decide⟩,⟨608,by decide⟩,⟨608,by decide⟩] | _ => ![⟨35,by decide⟩,⟨609,by decide⟩,⟨609,by decide⟩]

def ntree13LRLLRLLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨207,by decide⟩,⟨610,by decide⟩,⟨610,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨611,by decide⟩] | 2 => ![⟨221,by decide⟩,⟨388,by decide⟩,⟨612,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨605,by decide⟩,⟨613,by decide⟩] | _ => ![⟨219,by decide⟩,⟨606,by decide⟩,⟨614,by decide⟩]

def ntree13LRLLRLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLLRLLRL i else ntree13LRLLRLLRR (i - 4)

def ntree13LRLLRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LRLLRLLL i else ntree13LRLLRLLR (i - 9)

def ntree13LRLLRLRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨35,by decide⟩,⟨35,by decide⟩,⟨615,by decide⟩] | 1 => ![⟨220,by decide⟩,⟨388,by decide⟩,⟨616,by decide⟩] | 2 => ![⟨222,by decide⟩,⟨423,by decide⟩,⟨617,by decide⟩] | _ => ![⟨8,by decide⟩,⟨607,by decide⟩,⟨618,by decide⟩]

def ntree13LRLLRLRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨203,by decide⟩,⟨203,by decide⟩,⟨619,by decide⟩] | 1 => ![⟨219,by decide⟩,⟨608,by decide⟩,⟨620,by decide⟩] | 2 => ![⟨54,by decide⟩,⟨609,by decide⟩,⟨621,by decide⟩] | 3 => ![⟨224,by decide⟩,⟨606,by decide⟩,⟨622,by decide⟩] | _ => ![⟨225,by decide⟩,⟨610,by decide⟩,⟨623,by decide⟩]

def ntree13LRLLRLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLLRLRLL i else ntree13LRLLRLRLR (i - 4)

def ntree13LRLLRLRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨624,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨625,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨626,by decide⟩,⟨626,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨526,by decide⟩,⟨0,by decide⟩] | _ => ![⟨384,by decide⟩,⟨384,by decide⟩,⟨624,by decide⟩]

def ntree13LRLLRLRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨273,by decide⟩,⟨388,by decide⟩,⟨627,by decide⟩] | 1 => ![⟨274,by decide⟩,⟨390,by decide⟩,⟨628,by decide⟩] | 2 => ![⟨629,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | 3 => ![⟨630,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨631,by decide⟩,⟨378,by decide⟩,⟨273,by decide⟩]

def ntree13LRLLRLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LRLLRLRRL i else ntree13LRLLRLRRR (i - 5)

def ntree13LRLLRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LRLLRLRL i else ntree13LRLLRLRR (i - 9)

def ntree13LRLLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 18 then ntree13LRLLRLL i else ntree13LRLLRLR (i - 18)

def ntree13LRLLRRLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨632,by decide⟩,⟨386,by decide⟩,⟨137,by decide⟩] | 1 => ![⟨633,by decide⟩,⟨386,by decide⟩,⟨126,by decide⟩] | 2 => ![⟨634,by decide⟩,⟨381,by decide⟩,⟨274,by decide⟩] | _ => ![⟨635,by decide⟩,⟨384,by decide⟩,⟨126,by decide⟩]

def ntree13LRLLRRLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨636,by decide⟩,⟨394,by decide⟩,⟨627,by decide⟩] | 1 => ![⟨288,by decide⟩,⟨637,by decide⟩,⟨637,by decide⟩] | 2 => ![⟨638,by decide⟩,⟨639,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨640,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨639,by decide⟩,⟨639,by decide⟩,⟨0,by decide⟩]

def ntree13LRLLRRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLLRRLLL i else ntree13LRLLRRLLR (i - 4)

def ntree13LRLLRRLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨641,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨642,by decide⟩] | 2 => ![⟨386,by decide⟩,⟨386,by decide⟩,⟨542,by decide⟩] | 3 => ![⟨399,by decide⟩,⟨399,by decide⟩,⟨642,by decide⟩] | _ => ![⟨643,by decide⟩,⟨399,by decide⟩,⟨162,by decide⟩]

def ntree13LRLLRRLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨644,by decide⟩,⟨399,by decide⟩,⟨273,by decide⟩] | 1 => ![⟨645,by decide⟩,⟨39,by decide⟩,⟨39,by decide⟩] | 2 => ![⟨646,by decide⟩,⟨401,by decide⟩,⟨274,by decide⟩] | 3 => ![⟨647,by decide⟩,⟨404,by decide⟩,⟨156,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨648,by decide⟩]

def ntree13LRLLRRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LRLLRRLRL i else ntree13LRLLRRLRR (i - 5)

def ntree13LRLLRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LRLLRRLL i else ntree13LRLLRRLR (i - 9)

def ntree13LRLLRRRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨649,by decide⟩,⟨649,by decide⟩] | 1 => ![⟨650,by decide⟩,⟨399,by decide⟩,⟨137,by decide⟩] | 2 => ![⟨651,by decide⟩,⟨399,by decide⟩,⟨178,by decide⟩] | _ => ![⟨652,by decide⟩,⟨404,by decide⟩,⟨179,by decide⟩]

def ntree13LRLLRRRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨653,by decide⟩,⟨395,by decide⟩,⟨553,by decide⟩] | 1 => ![⟨653,by decide⟩,⟨386,by decide⟩,⟨178,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨654,by decide⟩] | 3 => ![⟨655,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨656,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13LRLLRRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLLRRRLL i else ntree13LRLLRRRLR (i - 4)

def ntree13LRLLRRRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨657,by decide⟩,⟨657,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨657,by decide⟩,⟨658,by decide⟩,⟨524,by decide⟩] | 2 => ![⟨659,by decide⟩,⟨657,by decide⟩,⟨269,by decide⟩] | 3 => ![⟨660,by decide⟩,⟨660,by decide⟩,⟨0,by decide⟩] | _ => ![⟨384,by decide⟩,⟨447,by decide⟩,⟨441,by decide⟩]

def ntree13LRLLRRRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨269,by decide⟩,⟨441,by decide⟩,⟨661,by decide⟩] | 1 => ![⟨662,by decide⟩,⟨662,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨663,by decide⟩,⟨663,by decide⟩,⟨188,by decide⟩] | 3 => ![⟨664,by decide⟩,⟨664,by decide⟩,⟨188,by decide⟩] | _ => ![⟨273,by decide⟩,⟨455,by decide⟩,⟨665,by decide⟩]

def ntree13LRLLRRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LRLLRRRRL i else ntree13LRLLRRRRR (i - 5)

def ntree13LRLLRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LRLLRRRL i else ntree13LRLLRRRR (i - 9)

def ntree13LRLLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 19 then ntree13LRLLRRL i else ntree13LRLLRRR (i - 19)

def ntree13LRLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 37 then ntree13LRLLRL i else ntree13LRLLRR (i - 37)

def ntree13LRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 74 then ntree13LRLLL i else ntree13LRLLR (i - 74)

def ntree13LRLRLLLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨657,by decide⟩,⟨666,by decide⟩,⟨455,by decide⟩] | 1 => ![⟨636,by decide⟩,⟨384,by decide⟩,⟨273,by decide⟩] | 2 => ![⟨667,by decide⟩,⟨657,by decide⟩,⟨74,by decide⟩] | _ => ![⟨288,by decide⟩,⟨668,by decide⟩,⟨288,by decide⟩]

def ntree13LRLRLLLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨669,by decide⟩,⟨77,by decide⟩,⟨77,by decide⟩] | 1 => ![⟨670,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨670,by decide⟩,⟨439,by decide⟩,⟨542,by decide⟩] | 3 => ![⟨671,by decide⟩,⟨35,by decide⟩,⟨35,by decide⟩] | _ => ![⟨672,by decide⟩,⟨672,by decide⟩,⟨0,by decide⟩]

def ntree13LRLRLLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLRLLLLL i else ntree13LRLRLLLLR (i - 4)

def ntree13LRLRLLLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨673,by decide⟩,⟨673,by decide⟩,⟨35,by decide⟩] | 1 => ![⟨670,by decide⟩,⟨441,by decide⟩,⟨441,by decide⟩] | 2 => ![⟨674,by decide⟩,⟨399,by decide⟩,⟨0,by decide⟩] | _ => ![⟨675,by decide⟩,⟨675,by decide⟩,⟨203,by decide⟩]

def ntree13LRLRLLLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨676,by decide⟩,⟨676,by decide⟩,⟨203,by decide⟩] | 1 => ![⟨677,by decide⟩,⟨677,by decide⟩,⟨207,by decide⟩] | 2 => ![⟨399,by decide⟩,⟨678,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13LRLRLLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLRLLLRL i else ntree13LRLRLLLRR (i - 4)

def ntree13LRLRLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LRLRLLLL i else ntree13LRLRLLLR (i - 9)

def ntree13LRLRLLRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨679,by decide⟩,⟨35,by decide⟩,⟨35,by decide⟩] | 2 => ![⟨680,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨681,by decide⟩,⟨399,by decide⟩,⟨344,by decide⟩]

def ntree13LRLRLLRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨682,by decide⟩,⟨682,by decide⟩] | 1 => ![⟨399,by decide⟩,⟨683,by decide⟩,⟨682,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨684,by decide⟩,⟨684,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨685,by decide⟩,⟨685,by decide⟩] | _ => ![⟨203,by decide⟩,⟨686,by decide⟩,⟨686,by decide⟩]

def ntree13LRLRLLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLRLLRLL i else ntree13LRLRLLRLR (i - 4)

def ntree13LRLRLLRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨567,by decide⟩,⟨439,by decide⟩,⟨624,by decide⟩] | 2 => ![⟨687,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | 3 => ![⟨137,by decide⟩,⟨439,by decide⟩,⟨137,by decide⟩] | _ => ![⟨655,by decide⟩,⟨388,by decide⟩,⟨388,by decide⟩]

def ntree13LRLRLLRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨688,by decide⟩,⟨500,by decide⟩,⟨126,by decide⟩] | 1 => ![⟨689,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨690,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨691,by decide⟩,⟨0,by decide⟩,⟨126,by decide⟩] | _ => ![⟨0,by decide⟩,⟨692,by decide⟩,⟨692,by decide⟩]

def ntree13LRLRLLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LRLRLLRRL i else ntree13LRLRLLRRR (i - 5)

def ntree13LRLRLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LRLRLLRL i else ntree13LRLRLLRR (i - 9)

def ntree13LRLRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 18 then ntree13LRLRLLL i else ntree13LRLRLLR (i - 18)

def ntree13LRLRLRLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨353,by decide⟩,⟨693,by decide⟩,⟨693,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨694,by decide⟩,⟨694,by decide⟩] | 2 => ![⟨356,by decide⟩,⟨695,by decide⟩,⟨695,by decide⟩] | _ => ![⟨0,by decide⟩,⟨696,by decide⟩,⟨0,by decide⟩]

def ntree13LRLRLRLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨4,by decide⟩,⟨697,by decide⟩,⟨4,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨698,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨378,by decide⟩,⟨699,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨698,by decide⟩,⟨8,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13LRLRLRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLRLRLLL i else ntree13LRLRLRLLR (i - 4)

def ntree13LRLRLRLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨377,by decide⟩,⟨699,by decide⟩,⟨10,by decide⟩] | 1 => ![⟨379,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | 2 => ![⟨700,by decide⟩,⟨388,by decide⟩,⟨701,by decide⟩] | 3 => ![⟨378,by decide⟩,⟨378,by decide⟩,⟨16,by decide⟩] | _ => ![⟨25,by decide⟩,⟨388,by decide⟩,⟨388,by decide⟩]

def ntree13LRLRLRLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨702,by decide⟩,⟨703,by decide⟩,⟨703,by decide⟩] | 1 => ![⟨704,by decide⟩,⟨703,by decide⟩,⟨705,by decide⟩] | 2 => ![⟨32,by decide⟩,⟨706,by decide⟩,⟨388,by decide⟩] | 3 => ![⟨707,by decide⟩,⟨703,by decide⟩,⟨703,by decide⟩] | _ => ![⟨708,by decide⟩,⟨708,by decide⟩,⟨708,by decide⟩]

def ntree13LRLRLRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LRLRLRLRL i else ntree13LRLRLRLRR (i - 5)

def ntree13LRLRLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LRLRLRLL i else ntree13LRLRLRLR (i - 9)

def ntree13LRLRLRRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨708,by decide⟩,⟨709,by decide⟩,⟨709,by decide⟩] | 1 => ![⟨710,by decide⟩,⟨710,by decide⟩,⟨710,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨711,by decide⟩,⟨711,by decide⟩] | _ => ![⟨399,by decide⟩,⟨712,by decide⟩,⟨711,by decide⟩]

def ntree13LRLRLRRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨696,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨713,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨399,by decide⟩,⟨714,by decide⟩,⟨2,by decide⟩] | _ => ![⟨4,by decide⟩,⟨715,by decide⟩,⟨4,by decide⟩]

def ntree13LRLRLRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLRLRRLL i else ntree13LRLRLRRLR (i - 4)

def ntree13LRLRLRRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨401,by decide⟩,⟨716,by decide⟩,⟨6,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨713,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨403,by decide⟩,⟨714,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨382,by decide⟩,⟨715,by decide⟩,⟨4,by decide⟩] | _ => ![⟨385,by decide⟩,⟨713,by decide⟩,⟨0,by decide⟩]

def ntree13LRLRLRRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨717,by decide⟩,⟨0,by decide⟩,⟨717,by decide⟩] | 1 => ![⟨717,by decide⟩,⟨0,by decide⟩,⟨718,by decide⟩] | 2 => ![⟨719,by decide⟩,⟨0,by decide⟩,⟨720,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨721,by decide⟩] | _ => ![⟨399,by decide⟩,⟨399,by decide⟩,⟨0,by decide⟩]

def ntree13LRLRLRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LRLRLRRRL i else ntree13LRLRLRRRR (i - 5)

def ntree13LRLRLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LRLRLRRL i else ntree13LRLRLRRR (i - 9)

def ntree13LRLRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 19 then ntree13LRLRLRL i else ntree13LRLRLRR (i - 19)

def ntree13LRLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 37 then ntree13LRLRLL i else ntree13LRLRLR (i - 37)

def ntree13LRLRRLLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨722,by decide⟩,⟨399,by decide⟩,⟨720,by decide⟩] | 1 => ![⟨723,by decide⟩,⟨723,by decide⟩,⟨723,by decide⟩] | 2 => ![⟨724,by decide⟩,⟨2,by decide⟩,⟨725,by decide⟩] | _ => ![⟨0,by decide⟩,⟨726,by decide⟩,⟨0,by decide⟩]

def ntree13LRLRRLLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨415,by decide⟩,⟨727,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨379,by decide⟩,⟨726,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨728,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨728,by decide⟩,⟨8,by decide⟩] | _ => ![⟨708,by decide⟩,⟨729,by decide⟩,⟨729,by decide⟩]

def ntree13LRLRRLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLRRLLLL i else ntree13LRLRRLLLR (i - 4)

def ntree13LRLRRLLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨730,by decide⟩,⟨730,by decide⟩] | 1 => ![⟨731,by decide⟩,⟨399,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨65,by decide⟩,⟨732,by decide⟩,⟨448,by decide⟩] | _ => ![⟨733,by decide⟩,⟨0,by decide⟩,⟨733,by decide⟩]

def ntree13LRLRRLLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨734,by decide⟩,⟨65,by decide⟩,⟨733,by decide⟩] | 1 => ![⟨735,by decide⟩,⟨736,by decide⟩,⟨736,by decide⟩] | 2 => ![⟨737,by decide⟩,⟨736,by decide⟩,⟨738,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨739,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨740,by decide⟩,⟨0,by decide⟩]

def ntree13LRLRRLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLRRLLRL i else ntree13LRLRRLLRR (i - 4)

def ntree13LRLRRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LRLRRLLL i else ntree13LRLRRLLR (i - 9)

def ntree13LRLRRLRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨65,by decide⟩,⟨741,by decide⟩,⟨455,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨742,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨457,by decide⟩,⟨740,by decide⟩,⟨16,by decide⟩] | _ => ![⟨735,by decide⟩,⟨735,by decide⟩,⟨735,by decide⟩]

def ntree13LRLRRLRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨735,by decide⟩,⟨735,by decide⟩,⟨743,by decide⟩] | 1 => ![⟨25,by decide⟩,⟨448,by decide⟩,⟨448,by decide⟩] | 2 => ![⟨744,by decide⟩,⟨744,by decide⟩,⟨708,by decide⟩] | 3 => ![⟨744,by decide⟩,⟨745,by decide⟩,⟨709,by decide⟩] | _ => ![⟨746,by decide⟩,⟨746,by decide⟩,⟨747,by decide⟩]

def ntree13LRLRRLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLRRLRLL i else ntree13LRLRRLRLR (i - 4)

def ntree13LRLRRLRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨747,by decide⟩,⟨747,by decide⟩,⟨747,by decide⟩] | 1 => ![⟨747,by decide⟩,⟨748,by decide⟩,⟨748,by decide⟩] | 2 => ![⟨746,by decide⟩,⟨749,by decide⟩,⟨748,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨696,by decide⟩,⟨471,by decide⟩] | _ => ![⟨750,by decide⟩,⟨399,by decide⟩,⟨733,by decide⟩]

def ntree13LRLRRLRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨751,by decide⟩,⟨752,by decide⟩,⟨448,by decide⟩] | 1 => ![⟨753,by decide⟩,⟨754,by decide⟩,⟨736,by decide⟩] | 2 => ![⟨755,by decide⟩,⟨2,by decide⟩,⟨756,by decide⟩] | 3 => ![⟨755,by decide⟩,⟨0,by decide⟩,⟨755,by decide⟩] | _ => ![⟨755,by decide⟩,⟨448,by decide⟩,⟨757,by decide⟩]

def ntree13LRLRRLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LRLRRLRRL i else ntree13LRLRRLRRR (i - 5)

def ntree13LRLRRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LRLRRLRL i else ntree13LRLRRLRR (i - 9)

def ntree13LRLRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 18 then ntree13LRLRRLL i else ntree13LRLRRLR (i - 18)

def ntree13LRLRRRLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨751,by decide⟩,⟨751,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨753,by decide⟩,⟨753,by decide⟩,⟨735,by decide⟩] | 2 => ![⟨758,by decide⟩,⟨746,by decide⟩,⟨759,by decide⟩] | _ => ![⟨759,by decide⟩,⟨747,by decide⟩,⟨759,by decide⟩]

def ntree13LRLRRRLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨760,by decide⟩,⟨65,by decide⟩,⟨761,by decide⟩] | 1 => ![⟨761,by decide⟩,⟨0,by decide⟩,⟨761,by decide⟩] | 2 => ![⟨737,by decide⟩,⟨735,by decide⟩,⟨737,by decide⟩] | 3 => ![⟨708,by decide⟩,⟨762,by decide⟩,⟨708,by decide⟩] | _ => ![⟨708,by decide⟩,⟨763,by decide⟩,⟨708,by decide⟩]

def ntree13LRLRRRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLRRRLLL i else ntree13LRLRRRLLR (i - 4)

def ntree13LRLRRRLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨764,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨765,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨399,by decide⟩,⟨766,by decide⟩,⟨93,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨767,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨768,by decide⟩,⟨0,by decide⟩]

def ntree13LRLRRRLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨98,by decide⟩,⟨769,by decide⟩,⟨489,by decide⟩] | 2 => ![⟨99,by decide⟩,⟨770,by decide⟩,⟨490,by decide⟩] | 3 => ![⟨65,by decide⟩,⟨771,by decide⟩,⟨388,by decide⟩] | _ => ![⟨4,by decide⟩,⟨772,by decide⟩,⟨4,by decide⟩]

def ntree13LRLRRRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LRLRRRLRL i else ntree13LRLRRRLRR (i - 5)

def ntree13LRLRRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LRLRRRLL i else ntree13LRLRRRLR (i - 9)

def ntree13LRLRRRRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨773,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨774,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨98,by decide⟩,⟨775,by decide⟩,⟨390,by decide⟩] | _ => ![⟨99,by decide⟩,⟨776,by decide⟩,⟨388,by decide⟩]

def ntree13LRLRRRRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨777,by decide⟩,⟨774,by decide⟩,⟨16,by decide⟩] | 1 => ![⟨735,by decide⟩,⟨778,by decide⟩,⟨778,by decide⟩] | 2 => ![⟨779,by decide⟩,⟨780,by decide⟩,⟨703,by decide⟩] | 3 => ![⟨781,by decide⟩,⟨782,by decide⟩,⟨2,by decide⟩] | _ => ![⟨105,by decide⟩,⟨783,by decide⟩,⟨501,by decide⟩]

def ntree13LRLRRRRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRLRRRRLL i else ntree13LRLRRRRLR (i - 4)

def ntree13LRLRRRRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨104,by decide⟩,⟨784,by decide⟩,⟨104,by decide⟩] | 1 => ![⟨785,by decide⟩,⟨786,by decide⟩,⟨786,by decide⟩] | 2 => ![⟨65,by decide⟩,⟨65,by decide⟩,⟨503,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨448,by decide⟩,⟨448,by decide⟩] | _ => ![⟨65,by decide⟩,⟨732,by decide⟩,⟨504,by decide⟩]

def ntree13LRLRRRRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨696,by decide⟩,⟨503,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨697,by decide⟩,⟨505,by decide⟩] | 2 => ![⟨65,by decide⟩,⟨787,by decide⟩,⟨515,by decide⟩] | 3 => ![⟨69,by decide⟩,⟨787,by decide⟩,⟨517,by decide⟩] | _ => ![⟨50,by decide⟩,⟨788,by decide⟩,⟨481,by decide⟩]

def ntree13LRLRRRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LRLRRRRRL i else ntree13LRLRRRRRR (i - 5)

def ntree13LRLRRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LRLRRRRL i else ntree13LRLRRRRR (i - 9)

def ntree13LRLRRR (i : Nat) : Fin 3 → Fin 2085 := if i < 19 then ntree13LRLRRRL i else ntree13LRLRRRR (i - 19)

def ntree13LRLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 37 then ntree13LRLRRL i else ntree13LRLRRR (i - 37)

def ntree13LRLR (i : Nat) : Fin 3 → Fin 2085 := if i < 75 then ntree13LRLRL i else ntree13LRLRR (i - 75)

def ntree13LRL (i : Nat) : Fin 3 → Fin 2085 := if i < 149 then ntree13LRLL i else ntree13LRLR (i - 149)

def ntree13LRRLLLLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨789,by decide⟩,⟨0,by decide⟩,⟨789,by decide⟩] | 1 => ![⟨790,by decide⟩,⟨0,by decide⟩,⟨790,by decide⟩] | 2 => ![⟨791,by decide⟩,⟨792,by decide⟩,⟨791,by decide⟩] | _ => ![⟨792,by decide⟩,⟨792,by decide⟩,⟨792,by decide⟩]

def ntree13LRRLLLLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨793,by decide⟩,⟨0,by decide⟩,⟨789,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨792,by decide⟩,⟨794,by decide⟩,⟨794,by decide⟩] | 3 => ![⟨378,by decide⟩,⟨795,by decide⟩,⟨132,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13LRRLLLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRRLLLLLL i else ntree13LRRLLLLLR (i - 4)

def ntree13LRRLLLLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨789,by decide⟩,⟨388,by decide⟩,⟨796,by decide⟩] | _ => ![⟨791,by decide⟩,⟨794,by decide⟩,⟨797,by decide⟩]

def ntree13LRRLLLLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨378,by decide⟩,⟨378,by decide⟩,⟨139,by decide⟩] | 1 => ![⟨137,by decide⟩,⟨696,by decide⟩,⟨137,by decide⟩] | 2 => ![⟨534,by decide⟩,⟨798,by decide⟩,⟨132,by decide⟩] | 3 => ![⟨377,by decide⟩,⟨795,by decide⟩,⟨143,by decide⟩] | _ => ![⟨379,by decide⟩,⟨132,by decide⟩,⟨132,by decide⟩]

def ntree13LRRLLLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRRLLLLRL i else ntree13LRRLLLLRR (i - 4)

def ntree13LRRLLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LRRLLLLL i else ntree13LRRLLLLR (i - 9)

def ntree13LRRLLLRLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨793,by decide⟩,⟨388,by decide⟩,⟨796,by decide⟩] | 1 => ![⟨799,by decide⟩,⟨0,by decide⟩,⟨799,by decide⟩] | 2 => ![⟨799,by decide⟩,⟨118,by decide⟩,⟨800,by decide⟩] | _ => ![⟨801,by decide⟩,⟨708,by decide⟩,⟨801,by decide⟩]

def ntree13LRRLLLRLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨802,by decide⟩,⟨802,by decide⟩,⟨802,by decide⟩] | 1 => ![⟨799,by decide⟩,⟨696,by decide⟩,⟨799,by decide⟩] | 2 => ![⟨151,by decide⟩,⟨803,by decide⟩,⟨538,by decide⟩] | 3 => ![⟨804,by decide⟩,⟨151,by decide⟩,⟨799,by decide⟩] | _ => ![⟨415,by decide⟩,⟨805,by decide⟩,⟨118,by decide⟩]

def ntree13LRRLLLRL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRRLLLRLL i else ntree13LRRLLLRLR (i - 4)

def ntree13LRRLLLRRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨790,by decide⟩,⟨713,by decide⟩,⟨790,by decide⟩] | 1 => ![⟨379,by decide⟩,⟨713,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨806,by decide⟩,⟨708,by decide⟩,⟨806,by decide⟩] | 3 => ![⟨807,by decide⟩,⟨802,by decide⟩,⟨802,by decide⟩] | _ => ![⟨792,by decide⟩,⟨792,by decide⟩,⟨808,by decide⟩]

def ntree13LRRLLLRRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨799,by decide⟩,⟨158,by decide⟩,⟨809,by decide⟩] | 1 => ![⟨810,by decide⟩,⟨50,by decide⟩,⟨799,by decide⟩] | 2 => ![⟨379,by decide⟩,⟨0,by decide⟩,⟨139,by decide⟩] | 3 => ![⟨811,by decide⟩,⟨0,by decide⟩,⟨811,by decide⟩] | _ => ![⟨812,by decide⟩,⟨708,by decide⟩,⟨812,by decide⟩]

def ntree13LRRLLLRR (i : Nat) : Fin 3 → Fin 2085 := if i < 5 then ntree13LRRLLLRRL i else ntree13LRRLLLRRR (i - 5)

def ntree13LRRLLLR (i : Nat) : Fin 3 → Fin 2085 := if i < 9 then ntree13LRRLLLRL i else ntree13LRRLLLRR (i - 9)

def ntree13LRRLLL (i : Nat) : Fin 3 → Fin 2085 := if i < 18 then ntree13LRRLLLL i else ntree13LRRLLLR (i - 18)

def ntree13LRRLLRLLL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨813,by decide⟩,⟨802,by decide⟩,⟨813,by decide⟩] | 1 => ![⟨814,by decide⟩,⟨708,by decide⟩,⟨814,by decide⟩] | 2 => ![⟨802,by decide⟩,⟨815,by decide⟩,⟨815,by decide⟩] | _ => ![⟨415,by decide⟩,⟨816,by decide⟩,⟨132,by decide⟩]

def ntree13LRRLLRLLR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨817,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨818,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨819,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨151,by decide⟩,⟨820,by decide⟩,⟨388,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree13LRRLLRLL (i : Nat) : Fin 3 → Fin 2085 := if i < 4 then ntree13LRRLLRLLL i else ntree13LRRLLRLLR (i - 4)

def ntree13LRRLLRLRL (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨821,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨821,by decide⟩,⟨8,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨822,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨696,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨823,by decide⟩,⟨448,by decide⟩]

def ntree13LRRLLRLRR (i : Nat) : Fin 3 → Fin 2085 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨824,by decide⟩,⟨65,by decide⟩,⟨825,by decide⟩] | 2 => ![⟨826,by decide⟩,⟨0,by decide⟩,⟨827,by decide⟩] | 3 => ![⟨826,by decide⟩,⟨132,by decide⟩,⟨828,by decide⟩] | _ => ![⟨826,by decide⟩,⟨448,by decide⟩,⟨829,by decide⟩]

end Paper2.Certificates.Q6.Coverage
