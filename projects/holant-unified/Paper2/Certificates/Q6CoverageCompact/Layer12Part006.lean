import Paper2.Certificates.Q6CoverageCompact.Layer12Part005

namespace Paper2.Certificates.Q6.Coverage

def stree12RLRLRLRLL (i : Nat) : State := match i with | 0 => state12_1590 | 1 => state12_1591 | 2 => state12_1592 | _ => state12_1593

def stree12RLRLRLRLR (i : Nat) : State := match i with | 0 => state12_1594 | 1 => state12_1595 | 2 => state12_1596 | 3 => state12_1597 | _ => state12_1598

def stree12RLRLRLRL (i : Nat) : State := if i < 4 then stree12RLRLRLRLL i else stree12RLRLRLRLR (i - 4)

def stree12RLRLRLRRL (i : Nat) : State := match i with | 0 => state12_1599 | 1 => state12_1600 | 2 => state12_1601 | 3 => state12_1602 | _ => state12_1603

def stree12RLRLRLRRR (i : Nat) : State := match i with | 0 => state12_1604 | 1 => state12_1605 | 2 => state12_1606 | 3 => state12_1607 | _ => state12_1608

def stree12RLRLRLRR (i : Nat) : State := if i < 5 then stree12RLRLRLRRL i else stree12RLRLRLRRR (i - 5)

def stree12RLRLRLR (i : Nat) : State := if i < 9 then stree12RLRLRLRL i else stree12RLRLRLRR (i - 9)

def stree12RLRLRL (i : Nat) : State := if i < 18 then stree12RLRLRLL i else stree12RLRLRLR (i - 18)

def stree12RLRLRRLLL (i : Nat) : State := match i with | 0 => state12_1609 | 1 => state12_1610 | 2 => state12_1611 | _ => state12_1612

def stree12RLRLRRLLR (i : Nat) : State := match i with | 0 => state12_1613 | 1 => state12_1614 | 2 => state12_1615 | 3 => state12_1616 | _ => state12_1617

def stree12RLRLRRLL (i : Nat) : State := if i < 4 then stree12RLRLRRLLL i else stree12RLRLRRLLR (i - 4)

def stree12RLRLRRLRL (i : Nat) : State := match i with | 0 => state12_1618 | 1 => state12_1619 | 2 => state12_1620 | 3 => state12_1621 | _ => state12_1622

def stree12RLRLRRLRR (i : Nat) : State := match i with | 0 => state12_1623 | 1 => state12_1624 | 2 => state12_1625 | 3 => state12_1626 | _ => state12_1627

def stree12RLRLRRLR (i : Nat) : State := if i < 5 then stree12RLRLRRLRL i else stree12RLRLRRLRR (i - 5)

def stree12RLRLRRL (i : Nat) : State := if i < 9 then stree12RLRLRRLL i else stree12RLRLRRLR (i - 9)

def stree12RLRLRRRLL (i : Nat) : State := match i with | 0 => state12_1628 | 1 => state12_1629 | 2 => state12_1630 | _ => state12_1631

def stree12RLRLRRRLR (i : Nat) : State := match i with | 0 => state12_1632 | 1 => state12_1633 | 2 => state12_1634 | 3 => state12_1635 | _ => state12_1636

def stree12RLRLRRRL (i : Nat) : State := if i < 4 then stree12RLRLRRRLL i else stree12RLRLRRRLR (i - 4)

def stree12RLRLRRRRL (i : Nat) : State := match i with | 0 => state12_1637 | 1 => state12_1638 | 2 => state12_1639 | 3 => state12_1640 | _ => state12_1641

def stree12RLRLRRRRR (i : Nat) : State := match i with | 0 => state12_1642 | 1 => state12_1643 | 2 => state12_1644 | 3 => state12_1645 | _ => state12_1646

def stree12RLRLRRRR (i : Nat) : State := if i < 5 then stree12RLRLRRRRL i else stree12RLRLRRRRR (i - 5)

def stree12RLRLRRR (i : Nat) : State := if i < 9 then stree12RLRLRRRL i else stree12RLRLRRRR (i - 9)

def stree12RLRLRR (i : Nat) : State := if i < 19 then stree12RLRLRRL i else stree12RLRLRRR (i - 19)

def stree12RLRLR (i : Nat) : State := if i < 37 then stree12RLRLRL i else stree12RLRLRR (i - 37)

def stree12RLRL (i : Nat) : State := if i < 75 then stree12RLRLL i else stree12RLRLR (i - 75)

def stree12RLRRLLLLL (i : Nat) : State := match i with | 0 => state12_1647 | 1 => state12_1648 | 2 => state12_1649 | _ => state12_1650

def stree12RLRRLLLLR (i : Nat) : State := match i with | 0 => state12_1651 | 1 => state12_1652 | 2 => state12_1653 | 3 => state12_1654 | _ => state12_1655

def stree12RLRRLLLL (i : Nat) : State := if i < 4 then stree12RLRRLLLLL i else stree12RLRRLLLLR (i - 4)

def stree12RLRRLLLRL (i : Nat) : State := match i with | 0 => state12_1656 | 1 => state12_1657 | 2 => state12_1658 | _ => state12_1659

def stree12RLRRLLLRR (i : Nat) : State := match i with | 0 => state12_1660 | 1 => state12_1661 | 2 => state12_1662 | 3 => state12_1663 | _ => state12_1664

def stree12RLRRLLLR (i : Nat) : State := if i < 4 then stree12RLRRLLLRL i else stree12RLRRLLLRR (i - 4)

def stree12RLRRLLL (i : Nat) : State := if i < 9 then stree12RLRRLLLL i else stree12RLRRLLLR (i - 9)

def stree12RLRRLLRLL (i : Nat) : State := match i with | 0 => state12_1665 | 1 => state12_1666 | 2 => state12_1667 | _ => state12_1668

def stree12RLRRLLRLR (i : Nat) : State := match i with | 0 => state12_1669 | 1 => state12_1670 | 2 => state12_1671 | 3 => state12_1672 | _ => state12_1673

def stree12RLRRLLRL (i : Nat) : State := if i < 4 then stree12RLRRLLRLL i else stree12RLRRLLRLR (i - 4)

def stree12RLRRLLRRL (i : Nat) : State := match i with | 0 => state12_1674 | 1 => state12_1675 | 2 => state12_1676 | 3 => state12_1677 | _ => state12_1678

def stree12RLRRLLRRR (i : Nat) : State := match i with | 0 => state12_1679 | 1 => state12_1680 | 2 => state12_1681 | 3 => state12_1682 | _ => state12_1683

def stree12RLRRLLRR (i : Nat) : State := if i < 5 then stree12RLRRLLRRL i else stree12RLRRLLRRR (i - 5)

def stree12RLRRLLR (i : Nat) : State := if i < 9 then stree12RLRRLLRL i else stree12RLRRLLRR (i - 9)

def stree12RLRRLL (i : Nat) : State := if i < 18 then stree12RLRRLLL i else stree12RLRRLLR (i - 18)

def stree12RLRRLRLLL (i : Nat) : State := match i with | 0 => state12_1684 | 1 => state12_1685 | 2 => state12_1686 | _ => state12_1687

def stree12RLRRLRLLR (i : Nat) : State := match i with | 0 => state12_1688 | 1 => state12_1689 | 2 => state12_1690 | 3 => state12_1691 | _ => state12_1692

def stree12RLRRLRLL (i : Nat) : State := if i < 4 then stree12RLRRLRLLL i else stree12RLRRLRLLR (i - 4)

def stree12RLRRLRLRL (i : Nat) : State := match i with | 0 => state12_1693 | 1 => state12_1694 | 2 => state12_1695 | 3 => state12_1696 | _ => state12_1697

def stree12RLRRLRLRR (i : Nat) : State := match i with | 0 => state12_1698 | 1 => state12_1699 | 2 => state12_1700 | 3 => state12_1701 | _ => state12_1702

def stree12RLRRLRLR (i : Nat) : State := if i < 5 then stree12RLRRLRLRL i else stree12RLRRLRLRR (i - 5)

def stree12RLRRLRL (i : Nat) : State := if i < 9 then stree12RLRRLRLL i else stree12RLRRLRLR (i - 9)

def stree12RLRRLRRLL (i : Nat) : State := match i with | 0 => state12_1703 | 1 => state12_1704 | 2 => state12_1705 | _ => state12_1706

def stree12RLRRLRRLR (i : Nat) : State := match i with | 0 => state12_1707 | 1 => state12_1708 | 2 => state12_1709 | 3 => state12_1710 | _ => state12_1711

def stree12RLRRLRRL (i : Nat) : State := if i < 4 then stree12RLRRLRRLL i else stree12RLRRLRRLR (i - 4)

def stree12RLRRLRRRL (i : Nat) : State := match i with | 0 => state12_1712 | 1 => state12_1713 | 2 => state12_1714 | 3 => state12_1715 | _ => state12_1716

def stree12RLRRLRRRR (i : Nat) : State := match i with | 0 => state12_1717 | 1 => state12_1718 | 2 => state12_1719 | 3 => state12_1720 | _ => state12_1721

def stree12RLRRLRRR (i : Nat) : State := if i < 5 then stree12RLRRLRRRL i else stree12RLRRLRRRR (i - 5)

def stree12RLRRLRR (i : Nat) : State := if i < 9 then stree12RLRRLRRL i else stree12RLRRLRRR (i - 9)

def stree12RLRRLR (i : Nat) : State := if i < 19 then stree12RLRRLRL i else stree12RLRRLRR (i - 19)

def stree12RLRRL (i : Nat) : State := if i < 37 then stree12RLRRLL i else stree12RLRRLR (i - 37)

def stree12RLRRRLLLL (i : Nat) : State := match i with | 0 => state12_1722 | 1 => state12_1723 | 2 => state12_1724 | _ => state12_1725

def stree12RLRRRLLLR (i : Nat) : State := match i with | 0 => state12_1726 | 1 => state12_1727 | 2 => state12_1728 | 3 => state12_1729 | _ => state12_1730

def stree12RLRRRLLL (i : Nat) : State := if i < 4 then stree12RLRRRLLLL i else stree12RLRRRLLLR (i - 4)

def stree12RLRRRLLRL (i : Nat) : State := match i with | 0 => state12_1731 | 1 => state12_1732 | 2 => state12_1733 | _ => state12_1734

def stree12RLRRRLLRR (i : Nat) : State := match i with | 0 => state12_1735 | 1 => state12_1736 | 2 => state12_1737 | 3 => state12_1738 | _ => state12_1739

def stree12RLRRRLLR (i : Nat) : State := if i < 4 then stree12RLRRRLLRL i else stree12RLRRRLLRR (i - 4)

def stree12RLRRRLL (i : Nat) : State := if i < 9 then stree12RLRRRLLL i else stree12RLRRRLLR (i - 9)

def stree12RLRRRLRLL (i : Nat) : State := match i with | 0 => state12_1740 | 1 => state12_1741 | 2 => state12_1742 | _ => state12_1743

def stree12RLRRRLRLR (i : Nat) : State := match i with | 0 => state12_1744 | 1 => state12_1745 | 2 => state12_1746 | 3 => state12_1747 | _ => state12_1748

def stree12RLRRRLRL (i : Nat) : State := if i < 4 then stree12RLRRRLRLL i else stree12RLRRRLRLR (i - 4)

def stree12RLRRRLRRL (i : Nat) : State := match i with | 0 => state12_1749 | 1 => state12_1750 | 2 => state12_1751 | 3 => state12_1752 | _ => state12_1753

def stree12RLRRRLRRR (i : Nat) : State := match i with | 0 => state12_1754 | 1 => state12_1755 | 2 => state12_1756 | 3 => state12_1757 | _ => state12_1758

def stree12RLRRRLRR (i : Nat) : State := if i < 5 then stree12RLRRRLRRL i else stree12RLRRRLRRR (i - 5)

def stree12RLRRRLR (i : Nat) : State := if i < 9 then stree12RLRRRLRL i else stree12RLRRRLRR (i - 9)

def stree12RLRRRL (i : Nat) : State := if i < 18 then stree12RLRRRLL i else stree12RLRRRLR (i - 18)

def stree12RLRRRRLLL (i : Nat) : State := match i with | 0 => state12_1759 | 1 => state12_1760 | 2 => state12_1761 | _ => state12_1762

def stree12RLRRRRLLR (i : Nat) : State := match i with | 0 => state12_1763 | 1 => state12_1764 | 2 => state12_1765 | 3 => state12_1766 | _ => state12_1767

def stree12RLRRRRLL (i : Nat) : State := if i < 4 then stree12RLRRRRLLL i else stree12RLRRRRLLR (i - 4)

def stree12RLRRRRLRL (i : Nat) : State := match i with | 0 => state12_1768 | 1 => state12_1769 | 2 => state12_1770 | 3 => state12_1771 | _ => state12_1772

def stree12RLRRRRLRR (i : Nat) : State := match i with | 0 => state12_1773 | 1 => state12_1774 | 2 => state12_1775 | 3 => state12_1776 | _ => state12_1777

def stree12RLRRRRLR (i : Nat) : State := if i < 5 then stree12RLRRRRLRL i else stree12RLRRRRLRR (i - 5)

def stree12RLRRRRL (i : Nat) : State := if i < 9 then stree12RLRRRRLL i else stree12RLRRRRLR (i - 9)

def stree12RLRRRRRLL (i : Nat) : State := match i with | 0 => state12_1778 | 1 => state12_1779 | 2 => state12_1780 | _ => state12_1781

def stree12RLRRRRRLR (i : Nat) : State := match i with | 0 => state12_1782 | 1 => state12_1783 | 2 => state12_1784 | 3 => state12_1785 | _ => state12_1786

def stree12RLRRRRRL (i : Nat) : State := if i < 4 then stree12RLRRRRRLL i else stree12RLRRRRRLR (i - 4)

def stree12RLRRRRRRL (i : Nat) : State := match i with | 0 => state12_1787 | 1 => state12_1788 | 2 => state12_1789 | 3 => state12_1790 | _ => state12_1791

def stree12RLRRRRRRR (i : Nat) : State := match i with | 0 => state12_1792 | 1 => state12_1793 | 2 => state12_1794 | 3 => state12_1795 | _ => state12_1796

def stree12RLRRRRRR (i : Nat) : State := if i < 5 then stree12RLRRRRRRL i else stree12RLRRRRRRR (i - 5)

def stree12RLRRRRR (i : Nat) : State := if i < 9 then stree12RLRRRRRL i else stree12RLRRRRRR (i - 9)

def stree12RLRRRR (i : Nat) : State := if i < 19 then stree12RLRRRRL i else stree12RLRRRRR (i - 19)

def stree12RLRRR (i : Nat) : State := if i < 37 then stree12RLRRRL i else stree12RLRRRR (i - 37)

def stree12RLRR (i : Nat) : State := if i < 75 then stree12RLRRL i else stree12RLRRR (i - 75)

def stree12RLR (i : Nat) : State := if i < 150 then stree12RLRL i else stree12RLRR (i - 150)

def stree12RL (i : Nat) : State := if i < 299 then stree12RLL i else stree12RLR (i - 299)

def stree12RRLLLLLLL (i : Nat) : State := match i with | 0 => state12_1797 | 1 => state12_1798 | 2 => state12_1799 | _ => state12_1800

def stree12RRLLLLLLR (i : Nat) : State := match i with | 0 => state12_1801 | 1 => state12_1802 | 2 => state12_1803 | 3 => state12_1804 | _ => state12_1805

def stree12RRLLLLLL (i : Nat) : State := if i < 4 then stree12RRLLLLLLL i else stree12RRLLLLLLR (i - 4)

def stree12RRLLLLLRL (i : Nat) : State := match i with | 0 => state12_1806 | 1 => state12_1807 | 2 => state12_1808 | _ => state12_1809

def stree12RRLLLLLRR (i : Nat) : State := match i with | 0 => state12_1810 | 1 => state12_1811 | 2 => state12_1812 | 3 => state12_1813 | _ => state12_1814

def stree12RRLLLLLR (i : Nat) : State := if i < 4 then stree12RRLLLLLRL i else stree12RRLLLLLRR (i - 4)

def stree12RRLLLLL (i : Nat) : State := if i < 9 then stree12RRLLLLLL i else stree12RRLLLLLR (i - 9)

def stree12RRLLLLRLL (i : Nat) : State := match i with | 0 => state12_1815 | 1 => state12_1816 | 2 => state12_1817 | _ => state12_1818

def stree12RRLLLLRLR (i : Nat) : State := match i with | 0 => state12_1819 | 1 => state12_1820 | 2 => state12_1821 | 3 => state12_1822 | _ => state12_1823

def stree12RRLLLLRL (i : Nat) : State := if i < 4 then stree12RRLLLLRLL i else stree12RRLLLLRLR (i - 4)

def stree12RRLLLLRRL (i : Nat) : State := match i with | 0 => state12_1824 | 1 => state12_1825 | 2 => state12_1826 | 3 => state12_1827 | _ => state12_1828

def stree12RRLLLLRRR (i : Nat) : State := match i with | 0 => state12_1829 | 1 => state12_1830 | 2 => state12_1831 | 3 => state12_1832 | _ => state12_1833

def stree12RRLLLLRR (i : Nat) : State := if i < 5 then stree12RRLLLLRRL i else stree12RRLLLLRRR (i - 5)

def stree12RRLLLLR (i : Nat) : State := if i < 9 then stree12RRLLLLRL i else stree12RRLLLLRR (i - 9)

def stree12RRLLLL (i : Nat) : State := if i < 18 then stree12RRLLLLL i else stree12RRLLLLR (i - 18)

def stree12RRLLLRLLL (i : Nat) : State := match i with | 0 => state12_1834 | 1 => state12_1835 | 2 => state12_1836 | _ => state12_1837

def stree12RRLLLRLLR (i : Nat) : State := match i with | 0 => state12_1838 | 1 => state12_1839 | 2 => state12_1840 | 3 => state12_1841 | _ => state12_1842

def stree12RRLLLRLL (i : Nat) : State := if i < 4 then stree12RRLLLRLLL i else stree12RRLLLRLLR (i - 4)

def stree12RRLLLRLRL (i : Nat) : State := match i with | 0 => state12_1843 | 1 => state12_1844 | 2 => state12_1845 | _ => state12_1846

def stree12RRLLLRLRR (i : Nat) : State := match i with | 0 => state12_1847 | 1 => state12_1848 | 2 => state12_1849 | 3 => state12_1850 | _ => state12_1851

def stree12RRLLLRLR (i : Nat) : State := if i < 4 then stree12RRLLLRLRL i else stree12RRLLLRLRR (i - 4)

def stree12RRLLLRL (i : Nat) : State := if i < 9 then stree12RRLLLRLL i else stree12RRLLLRLR (i - 9)

def stree12RRLLLRRLL (i : Nat) : State := match i with | 0 => state12_1852 | 1 => state12_1853 | 2 => state12_1854 | _ => state12_1855

def stree12RRLLLRRLR (i : Nat) : State := match i with | 0 => state12_1856 | 1 => state12_1857 | 2 => state12_1858 | 3 => state12_1859 | _ => state12_1860

def stree12RRLLLRRL (i : Nat) : State := if i < 4 then stree12RRLLLRRLL i else stree12RRLLLRRLR (i - 4)

def stree12RRLLLRRRL (i : Nat) : State := match i with | 0 => state12_1861 | 1 => state12_1862 | 2 => state12_1863 | 3 => state12_1864 | _ => state12_1865

def stree12RRLLLRRRR (i : Nat) : State := match i with | 0 => state12_1866 | 1 => state12_1867 | 2 => state12_1868 | 3 => state12_1869 | _ => state12_1870

def stree12RRLLLRRR (i : Nat) : State := if i < 5 then stree12RRLLLRRRL i else stree12RRLLLRRRR (i - 5)

def stree12RRLLLRR (i : Nat) : State := if i < 9 then stree12RRLLLRRL i else stree12RRLLLRRR (i - 9)

def stree12RRLLLR (i : Nat) : State := if i < 18 then stree12RRLLLRL i else stree12RRLLLRR (i - 18)

def stree12RRLLL (i : Nat) : State := if i < 37 then stree12RRLLLL i else stree12RRLLLR (i - 37)

def stree12RRLLRLLLL (i : Nat) : State := match i with | 0 => state12_1871 | 1 => state12_1872 | 2 => state12_1873 | _ => state12_1874

def stree12RRLLRLLLR (i : Nat) : State := match i with | 0 => state12_1875 | 1 => state12_1876 | 2 => state12_1877 | 3 => state12_1878 | _ => state12_1879

def stree12RRLLRLLL (i : Nat) : State := if i < 4 then stree12RRLLRLLLL i else stree12RRLLRLLLR (i - 4)

def stree12RRLLRLLRL (i : Nat) : State := match i with | 0 => state12_1880 | 1 => state12_1881 | 2 => state12_1882 | _ => state12_1883

def stree12RRLLRLLRR (i : Nat) : State := match i with | 0 => state12_1884 | 1 => state12_1885 | 2 => state12_1886 | 3 => state12_1887 | _ => state12_1888

def stree12RRLLRLLR (i : Nat) : State := if i < 4 then stree12RRLLRLLRL i else stree12RRLLRLLRR (i - 4)

def stree12RRLLRLL (i : Nat) : State := if i < 9 then stree12RRLLRLLL i else stree12RRLLRLLR (i - 9)

def stree12RRLLRLRLL (i : Nat) : State := match i with | 0 => state12_1889 | 1 => state12_1890 | 2 => state12_1891 | _ => state12_1892

def stree12RRLLRLRLR (i : Nat) : State := match i with | 0 => state12_1893 | 1 => state12_1894 | 2 => state12_1895 | 3 => state12_1896 | _ => state12_1897

def stree12RRLLRLRL (i : Nat) : State := if i < 4 then stree12RRLLRLRLL i else stree12RRLLRLRLR (i - 4)

def stree12RRLLRLRRL (i : Nat) : State := match i with | 0 => state12_1898 | 1 => state12_1899 | 2 => state12_1900 | 3 => state12_1901 | _ => state12_1902

def stree12RRLLRLRRR (i : Nat) : State := match i with | 0 => state12_1903 | 1 => state12_1904 | 2 => state12_1905 | 3 => state12_1906 | _ => state12_1907

def stree12RRLLRLRR (i : Nat) : State := if i < 5 then stree12RRLLRLRRL i else stree12RRLLRLRRR (i - 5)

def stree12RRLLRLR (i : Nat) : State := if i < 9 then stree12RRLLRLRL i else stree12RRLLRLRR (i - 9)

def stree12RRLLRL (i : Nat) : State := if i < 18 then stree12RRLLRLL i else stree12RRLLRLR (i - 18)

def stree12RRLLRRLLL (i : Nat) : State := match i with | 0 => state12_1908 | 1 => state12_1909 | 2 => state12_1910 | _ => state12_1911

def stree12RRLLRRLLR (i : Nat) : State := match i with | 0 => state12_1912 | 1 => state12_1913 | 2 => state12_1914 | 3 => state12_1915 | _ => state12_1916

def stree12RRLLRRLL (i : Nat) : State := if i < 4 then stree12RRLLRRLLL i else stree12RRLLRRLLR (i - 4)

def stree12RRLLRRLRL (i : Nat) : State := match i with | 0 => state12_1917 | 1 => state12_1918 | 2 => state12_1919 | 3 => state12_1920 | _ => state12_1921

def stree12RRLLRRLRR (i : Nat) : State := match i with | 0 => state12_1922 | 1 => state12_1923 | 2 => state12_1924 | 3 => state12_1925 | _ => state12_1926

def stree12RRLLRRLR (i : Nat) : State := if i < 5 then stree12RRLLRRLRL i else stree12RRLLRRLRR (i - 5)

def stree12RRLLRRL (i : Nat) : State := if i < 9 then stree12RRLLRRLL i else stree12RRLLRRLR (i - 9)

def stree12RRLLRRRLL (i : Nat) : State := match i with | 0 => state12_1927 | 1 => state12_1928 | 2 => state12_1929 | _ => state12_1930

def stree12RRLLRRRLR (i : Nat) : State := match i with | 0 => state12_1931 | 1 => state12_1932 | 2 => state12_1933 | 3 => state12_1934 | _ => state12_1935

def stree12RRLLRRRL (i : Nat) : State := if i < 4 then stree12RRLLRRRLL i else stree12RRLLRRRLR (i - 4)

def stree12RRLLRRRRL (i : Nat) : State := match i with | 0 => state12_1936 | 1 => state12_1937 | 2 => state12_1938 | 3 => state12_1939 | _ => state12_1940

def stree12RRLLRRRRR (i : Nat) : State := match i with | 0 => state12_1941 | 1 => state12_1942 | 2 => state12_1943 | 3 => state12_1944 | _ => state12_1945

def stree12RRLLRRRR (i : Nat) : State := if i < 5 then stree12RRLLRRRRL i else stree12RRLLRRRRR (i - 5)

def stree12RRLLRRR (i : Nat) : State := if i < 9 then stree12RRLLRRRL i else stree12RRLLRRRR (i - 9)

def stree12RRLLRR (i : Nat) : State := if i < 19 then stree12RRLLRRL i else stree12RRLLRRR (i - 19)

def stree12RRLLR (i : Nat) : State := if i < 37 then stree12RRLLRL i else stree12RRLLRR (i - 37)

def stree12RRLL (i : Nat) : State := if i < 74 then stree12RRLLL i else stree12RRLLR (i - 74)

def stree12RRLRLLLLL (i : Nat) : State := match i with | 0 => state12_1946 | 1 => state12_1947 | 2 => state12_1948 | _ => state12_1949

def stree12RRLRLLLLR (i : Nat) : State := match i with | 0 => state12_1950 | 1 => state12_1951 | 2 => state12_1952 | 3 => state12_1953 | _ => state12_1954

def stree12RRLRLLLL (i : Nat) : State := if i < 4 then stree12RRLRLLLLL i else stree12RRLRLLLLR (i - 4)

def stree12RRLRLLLRL (i : Nat) : State := match i with | 0 => state12_1955 | 1 => state12_1956 | 2 => state12_1957 | _ => state12_1958

def stree12RRLRLLLRR (i : Nat) : State := match i with | 0 => state12_1959 | 1 => state12_1960 | 2 => state12_1961 | 3 => state12_1962 | _ => state12_1963

def stree12RRLRLLLR (i : Nat) : State := if i < 4 then stree12RRLRLLLRL i else stree12RRLRLLLRR (i - 4)

def stree12RRLRLLL (i : Nat) : State := if i < 9 then stree12RRLRLLLL i else stree12RRLRLLLR (i - 9)

def stree12RRLRLLRLL (i : Nat) : State := match i with | 0 => state12_1964 | 1 => state12_1965 | 2 => state12_1966 | _ => state12_1967

def stree12RRLRLLRLR (i : Nat) : State := match i with | 0 => state12_1968 | 1 => state12_1969 | 2 => state12_1970 | 3 => state12_1971 | _ => state12_1972

def stree12RRLRLLRL (i : Nat) : State := if i < 4 then stree12RRLRLLRLL i else stree12RRLRLLRLR (i - 4)

def stree12RRLRLLRRL (i : Nat) : State := match i with | 0 => state12_1973 | 1 => state12_1974 | 2 => state12_1975 | 3 => state12_1976 | _ => state12_1977

def stree12RRLRLLRRR (i : Nat) : State := match i with | 0 => state12_1978 | 1 => state12_1979 | 2 => state12_1980 | 3 => state12_1981 | _ => state12_1982

def stree12RRLRLLRR (i : Nat) : State := if i < 5 then stree12RRLRLLRRL i else stree12RRLRLLRRR (i - 5)

def stree12RRLRLLR (i : Nat) : State := if i < 9 then stree12RRLRLLRL i else stree12RRLRLLRR (i - 9)

def stree12RRLRLL (i : Nat) : State := if i < 18 then stree12RRLRLLL i else stree12RRLRLLR (i - 18)

def stree12RRLRLRLLL (i : Nat) : State := match i with | 0 => state12_1983 | 1 => state12_1984 | 2 => state12_1985 | _ => state12_1986

def stree12RRLRLRLLR (i : Nat) : State := match i with | 0 => state12_1987 | 1 => state12_1988 | 2 => state12_1989 | 3 => state12_1990 | _ => state12_1991

def stree12RRLRLRLL (i : Nat) : State := if i < 4 then stree12RRLRLRLLL i else stree12RRLRLRLLR (i - 4)

def stree12RRLRLRLRL (i : Nat) : State := match i with | 0 => state12_1992 | 1 => state12_1993 | 2 => state12_1994 | 3 => state12_1995 | _ => state12_1996

def stree12RRLRLRLRR (i : Nat) : State := match i with | 0 => state12_1997 | 1 => state12_1998 | 2 => state12_1999 | 3 => state12_2000 | _ => state12_2001

def stree12RRLRLRLR (i : Nat) : State := if i < 5 then stree12RRLRLRLRL i else stree12RRLRLRLRR (i - 5)

def stree12RRLRLRL (i : Nat) : State := if i < 9 then stree12RRLRLRLL i else stree12RRLRLRLR (i - 9)

def stree12RRLRLRRLL (i : Nat) : State := match i with | 0 => state12_2002 | 1 => state12_2003 | 2 => state12_2004 | _ => state12_2005

def stree12RRLRLRRLR (i : Nat) : State := match i with | 0 => state12_2006 | 1 => state12_2007 | 2 => state12_2008 | 3 => state12_2009 | _ => state12_2010

def stree12RRLRLRRL (i : Nat) : State := if i < 4 then stree12RRLRLRRLL i else stree12RRLRLRRLR (i - 4)

def stree12RRLRLRRRL (i : Nat) : State := match i with | 0 => state12_2011 | 1 => state12_2012 | 2 => state12_2013 | 3 => state12_2014 | _ => state12_2015

def stree12RRLRLRRRR (i : Nat) : State := match i with | 0 => state12_2016 | 1 => state12_2017 | 2 => state12_2018 | 3 => state12_2019 | _ => state12_2020

def stree12RRLRLRRR (i : Nat) : State := if i < 5 then stree12RRLRLRRRL i else stree12RRLRLRRRR (i - 5)

def stree12RRLRLRR (i : Nat) : State := if i < 9 then stree12RRLRLRRL i else stree12RRLRLRRR (i - 9)

def stree12RRLRLR (i : Nat) : State := if i < 19 then stree12RRLRLRL i else stree12RRLRLRR (i - 19)

def stree12RRLRL (i : Nat) : State := if i < 37 then stree12RRLRLL i else stree12RRLRLR (i - 37)

def stree12RRLRRLLLL (i : Nat) : State := match i with | 0 => state12_2021 | 1 => state12_2022 | 2 => state12_2023 | _ => state12_2024

def stree12RRLRRLLLR (i : Nat) : State := match i with | 0 => state12_2025 | 1 => state12_2026 | 2 => state12_2027 | 3 => state12_2028 | _ => state12_2029

def stree12RRLRRLLL (i : Nat) : State := if i < 4 then stree12RRLRRLLLL i else stree12RRLRRLLLR (i - 4)

def stree12RRLRRLLRL (i : Nat) : State := match i with | 0 => state12_2030 | 1 => state12_2031 | 2 => state12_2032 | _ => state12_2033

def stree12RRLRRLLRR (i : Nat) : State := match i with | 0 => state12_2034 | 1 => state12_2035 | 2 => state12_2036 | 3 => state12_2037 | _ => state12_2038

def stree12RRLRRLLR (i : Nat) : State := if i < 4 then stree12RRLRRLLRL i else stree12RRLRRLLRR (i - 4)

def stree12RRLRRLL (i : Nat) : State := if i < 9 then stree12RRLRRLLL i else stree12RRLRRLLR (i - 9)

def stree12RRLRRLRLL (i : Nat) : State := match i with | 0 => state12_2039 | 1 => state12_2040 | 2 => state12_2041 | _ => state12_2042

def stree12RRLRRLRLR (i : Nat) : State := match i with | 0 => state12_2043 | 1 => state12_2044 | 2 => state12_2045 | 3 => state12_2046 | _ => state12_2047

def stree12RRLRRLRL (i : Nat) : State := if i < 4 then stree12RRLRRLRLL i else stree12RRLRRLRLR (i - 4)

def stree12RRLRRLRRL (i : Nat) : State := match i with | 0 => state12_2048 | 1 => state12_2049 | 2 => state12_2050 | 3 => state12_2051 | _ => state12_2052

def stree12RRLRRLRRR (i : Nat) : State := match i with | 0 => state12_2053 | 1 => state12_2054 | 2 => state12_2055 | 3 => state12_2056 | _ => state12_2057

def stree12RRLRRLRR (i : Nat) : State := if i < 5 then stree12RRLRRLRRL i else stree12RRLRRLRRR (i - 5)

def stree12RRLRRLR (i : Nat) : State := if i < 9 then stree12RRLRRLRL i else stree12RRLRRLRR (i - 9)

def stree12RRLRRL (i : Nat) : State := if i < 18 then stree12RRLRRLL i else stree12RRLRRLR (i - 18)

def stree12RRLRRRLLL (i : Nat) : State := match i with | 0 => state12_2058 | 1 => state12_2059 | 2 => state12_2060 | _ => state12_2061

def stree12RRLRRRLLR (i : Nat) : State := match i with | 0 => state12_2062 | 1 => state12_2063 | 2 => state12_2064 | 3 => state12_2065 | _ => state12_2066

def stree12RRLRRRLL (i : Nat) : State := if i < 4 then stree12RRLRRRLLL i else stree12RRLRRRLLR (i - 4)

def stree12RRLRRRLRL (i : Nat) : State := match i with | 0 => state12_2067 | 1 => state12_2068 | 2 => state12_2069 | 3 => state12_2070 | _ => state12_2071

def stree12RRLRRRLRR (i : Nat) : State := match i with | 0 => state12_2072 | 1 => state12_2073 | 2 => state12_2074 | 3 => state12_2075 | _ => state12_2076

def stree12RRLRRRLR (i : Nat) : State := if i < 5 then stree12RRLRRRLRL i else stree12RRLRRRLRR (i - 5)

def stree12RRLRRRL (i : Nat) : State := if i < 9 then stree12RRLRRRLL i else stree12RRLRRRLR (i - 9)

def stree12RRLRRRRLL (i : Nat) : State := match i with | 0 => state12_2077 | 1 => state12_2078 | 2 => state12_2079 | _ => state12_2080

def stree12RRLRRRRLR (i : Nat) : State := match i with | 0 => state12_2081 | 1 => state12_2082 | 2 => state12_2083 | 3 => state12_2084 | _ => state12_2085

def stree12RRLRRRRL (i : Nat) : State := if i < 4 then stree12RRLRRRRLL i else stree12RRLRRRRLR (i - 4)

def stree12RRLRRRRRL (i : Nat) : State := match i with | 0 => state12_2086 | 1 => state12_2087 | 2 => state12_2088 | 3 => state12_2089 | _ => state12_2090

def stree12RRLRRRRRR (i : Nat) : State := match i with | 0 => state12_2091 | 1 => state12_2092 | 2 => state12_2093 | 3 => state12_2094 | _ => state12_2095

def stree12RRLRRRRR (i : Nat) : State := if i < 5 then stree12RRLRRRRRL i else stree12RRLRRRRRR (i - 5)

def stree12RRLRRRR (i : Nat) : State := if i < 9 then stree12RRLRRRRL i else stree12RRLRRRRR (i - 9)

def stree12RRLRRR (i : Nat) : State := if i < 19 then stree12RRLRRRL i else stree12RRLRRRR (i - 19)

def stree12RRLRR (i : Nat) : State := if i < 37 then stree12RRLRRL i else stree12RRLRRR (i - 37)

def stree12RRLR (i : Nat) : State := if i < 75 then stree12RRLRL i else stree12RRLRR (i - 75)

def stree12RRL (i : Nat) : State := if i < 149 then stree12RRLL i else stree12RRLR (i - 149)

def stree12RRRLLLLLL (i : Nat) : State := match i with | 0 => state12_2096 | 1 => state12_2097 | 2 => state12_2098 | _ => state12_2099

def stree12RRRLLLLLR (i : Nat) : State := match i with | 0 => state12_2100 | 1 => state12_2101 | 2 => state12_2102 | 3 => state12_2103 | _ => state12_2104

def stree12RRRLLLLL (i : Nat) : State := if i < 4 then stree12RRRLLLLLL i else stree12RRRLLLLLR (i - 4)

def stree12RRRLLLLRL (i : Nat) : State := match i with | 0 => state12_2105 | 1 => state12_2106 | 2 => state12_2107 | _ => state12_2108

def stree12RRRLLLLRR (i : Nat) : State := match i with | 0 => state12_2109 | 1 => state12_2110 | 2 => state12_2111 | 3 => state12_2112 | _ => state12_2113

def stree12RRRLLLLR (i : Nat) : State := if i < 4 then stree12RRRLLLLRL i else stree12RRRLLLLRR (i - 4)

def stree12RRRLLLL (i : Nat) : State := if i < 9 then stree12RRRLLLLL i else stree12RRRLLLLR (i - 9)

def stree12RRRLLLRLL (i : Nat) : State := match i with | 0 => state12_2114 | 1 => state12_2115 | 2 => state12_2116 | _ => state12_2117

def stree12RRRLLLRLR (i : Nat) : State := match i with | 0 => state12_2118 | 1 => state12_2119 | 2 => state12_2120 | 3 => state12_2121 | _ => state12_2122

def stree12RRRLLLRL (i : Nat) : State := if i < 4 then stree12RRRLLLRLL i else stree12RRRLLLRLR (i - 4)

def stree12RRRLLLRRL (i : Nat) : State := match i with | 0 => state12_2123 | 1 => state12_2124 | 2 => state12_2125 | 3 => state12_2126 | _ => state12_2127

def stree12RRRLLLRRR (i : Nat) : State := match i with | 0 => state12_2128 | 1 => state12_2129 | 2 => state12_2130 | 3 => state12_2131 | _ => state12_2132

def stree12RRRLLLRR (i : Nat) : State := if i < 5 then stree12RRRLLLRRL i else stree12RRRLLLRRR (i - 5)

def stree12RRRLLLR (i : Nat) : State := if i < 9 then stree12RRRLLLRL i else stree12RRRLLLRR (i - 9)

def stree12RRRLLL (i : Nat) : State := if i < 18 then stree12RRRLLLL i else stree12RRRLLLR (i - 18)

def stree12RRRLLRLLL (i : Nat) : State := match i with | 0 => state12_2133 | 1 => state12_2134 | 2 => state12_2135 | _ => state12_2136

def stree12RRRLLRLLR (i : Nat) : State := match i with | 0 => state12_2137 | 1 => state12_2138 | 2 => state12_2139 | 3 => state12_2140 | _ => state12_2141

def stree12RRRLLRLL (i : Nat) : State := if i < 4 then stree12RRRLLRLLL i else stree12RRRLLRLLR (i - 4)

def stree12RRRLLRLRL (i : Nat) : State := match i with | 0 => state12_2142 | 1 => state12_2143 | 2 => state12_2144 | 3 => state12_2145 | _ => state12_2146

def stree12RRRLLRLRR (i : Nat) : State := match i with | 0 => state12_2147 | 1 => state12_2148 | 2 => state12_2149 | 3 => state12_2150 | _ => state12_2151

def stree12RRRLLRLR (i : Nat) : State := if i < 5 then stree12RRRLLRLRL i else stree12RRRLLRLRR (i - 5)

def stree12RRRLLRL (i : Nat) : State := if i < 9 then stree12RRRLLRLL i else stree12RRRLLRLR (i - 9)

def stree12RRRLLRRLL (i : Nat) : State := match i with | 0 => state12_2152 | 1 => state12_2153 | 2 => state12_2154 | _ => state12_2155

def stree12RRRLLRRLR (i : Nat) : State := match i with | 0 => state12_2156 | 1 => state12_2157 | 2 => state12_2158 | 3 => state12_2159 | _ => state12_2160

def stree12RRRLLRRL (i : Nat) : State := if i < 4 then stree12RRRLLRRLL i else stree12RRRLLRRLR (i - 4)

def stree12RRRLLRRRL (i : Nat) : State := match i with | 0 => state12_2161 | 1 => state12_2162 | 2 => state12_2163 | 3 => state12_2164 | _ => state12_2165

def stree12RRRLLRRRR (i : Nat) : State := match i with | 0 => state12_2166 | 1 => state12_2167 | 2 => state12_2168 | 3 => state12_2169 | _ => state12_2170

def stree12RRRLLRRR (i : Nat) : State := if i < 5 then stree12RRRLLRRRL i else stree12RRRLLRRRR (i - 5)

def stree12RRRLLRR (i : Nat) : State := if i < 9 then stree12RRRLLRRL i else stree12RRRLLRRR (i - 9)

def stree12RRRLLR (i : Nat) : State := if i < 19 then stree12RRRLLRL i else stree12RRRLLRR (i - 19)

def stree12RRRLL (i : Nat) : State := if i < 37 then stree12RRRLLL i else stree12RRRLLR (i - 37)

def stree12RRRLRLLLL (i : Nat) : State := match i with | 0 => state12_2171 | 1 => state12_2172 | 2 => state12_2173 | _ => state12_2174

def stree12RRRLRLLLR (i : Nat) : State := match i with | 0 => state12_2175 | 1 => state12_2176 | 2 => state12_2177 | 3 => state12_2178 | _ => state12_2179

def stree12RRRLRLLL (i : Nat) : State := if i < 4 then stree12RRRLRLLLL i else stree12RRRLRLLLR (i - 4)

def stree12RRRLRLLRL (i : Nat) : State := match i with | 0 => state12_2180 | 1 => state12_2181 | 2 => state12_2182 | _ => state12_2183

def stree12RRRLRLLRR (i : Nat) : State := match i with | 0 => state12_2184 | 1 => state12_2185 | 2 => state12_2186 | 3 => state12_2187 | _ => state12_2188

def stree12RRRLRLLR (i : Nat) : State := if i < 4 then stree12RRRLRLLRL i else stree12RRRLRLLRR (i - 4)

def stree12RRRLRLL (i : Nat) : State := if i < 9 then stree12RRRLRLLL i else stree12RRRLRLLR (i - 9)

def stree12RRRLRLRLL (i : Nat) : State := match i with | 0 => state12_2189 | 1 => state12_2190 | 2 => state12_2191 | _ => state12_2192

def stree12RRRLRLRLR (i : Nat) : State := match i with | 0 => state12_2193 | 1 => state12_2194 | 2 => state12_2195 | 3 => state12_2196 | _ => state12_2197

def stree12RRRLRLRL (i : Nat) : State := if i < 4 then stree12RRRLRLRLL i else stree12RRRLRLRLR (i - 4)

def stree12RRRLRLRRL (i : Nat) : State := match i with | 0 => state12_2198 | 1 => state12_2199 | 2 => state12_2200 | 3 => state12_2201 | _ => state12_2202

def stree12RRRLRLRRR (i : Nat) : State := match i with | 0 => state12_2203 | 1 => state12_2204 | 2 => state12_2205 | 3 => state12_2206 | _ => state12_2207

def stree12RRRLRLRR (i : Nat) : State := if i < 5 then stree12RRRLRLRRL i else stree12RRRLRLRRR (i - 5)

def stree12RRRLRLR (i : Nat) : State := if i < 9 then stree12RRRLRLRL i else stree12RRRLRLRR (i - 9)

def stree12RRRLRL (i : Nat) : State := if i < 18 then stree12RRRLRLL i else stree12RRRLRLR (i - 18)

def stree12RRRLRRLLL (i : Nat) : State := match i with | 0 => state12_2208 | 1 => state12_2209 | 2 => state12_2210 | _ => state12_2211

def stree12RRRLRRLLR (i : Nat) : State := match i with | 0 => state12_2212 | 1 => state12_2213 | 2 => state12_2214 | 3 => state12_2215 | _ => state12_2216

def stree12RRRLRRLL (i : Nat) : State := if i < 4 then stree12RRRLRRLLL i else stree12RRRLRRLLR (i - 4)

def stree12RRRLRRLRL (i : Nat) : State := match i with | 0 => state12_2217 | 1 => state12_2218 | 2 => state12_2219 | 3 => state12_2220 | _ => state12_2221

def stree12RRRLRRLRR (i : Nat) : State := match i with | 0 => state12_2222 | 1 => state12_2223 | 2 => state12_2224 | 3 => state12_2225 | _ => state12_2226

def stree12RRRLRRLR (i : Nat) : State := if i < 5 then stree12RRRLRRLRL i else stree12RRRLRRLRR (i - 5)

def stree12RRRLRRL (i : Nat) : State := if i < 9 then stree12RRRLRRLL i else stree12RRRLRRLR (i - 9)

def stree12RRRLRRRLL (i : Nat) : State := match i with | 0 => state12_2227 | 1 => state12_2228 | 2 => state12_2229 | _ => state12_2230

def stree12RRRLRRRLR (i : Nat) : State := match i with | 0 => state12_2231 | 1 => state12_2232 | 2 => state12_2233 | 3 => state12_2234 | _ => state12_2235

def stree12RRRLRRRL (i : Nat) : State := if i < 4 then stree12RRRLRRRLL i else stree12RRRLRRRLR (i - 4)

def stree12RRRLRRRRL (i : Nat) : State := match i with | 0 => state12_2236 | 1 => state12_2237 | 2 => state12_2238 | 3 => state12_2239 | _ => state12_2240

def stree12RRRLRRRRR (i : Nat) : State := match i with | 0 => state12_2241 | 1 => state12_2242 | 2 => state12_2243 | 3 => state12_2244 | _ => state12_2245

def stree12RRRLRRRR (i : Nat) : State := if i < 5 then stree12RRRLRRRRL i else stree12RRRLRRRRR (i - 5)

def stree12RRRLRRR (i : Nat) : State := if i < 9 then stree12RRRLRRRL i else stree12RRRLRRRR (i - 9)

def stree12RRRLRR (i : Nat) : State := if i < 19 then stree12RRRLRRL i else stree12RRRLRRR (i - 19)

def stree12RRRLR (i : Nat) : State := if i < 37 then stree12RRRLRL i else stree12RRRLRR (i - 37)

def stree12RRRL (i : Nat) : State := if i < 75 then stree12RRRLL i else stree12RRRLR (i - 75)

def stree12RRRRLLLLL (i : Nat) : State := match i with | 0 => state12_2246 | 1 => state12_2247 | 2 => state12_2248 | _ => state12_2249

def stree12RRRRLLLLR (i : Nat) : State := match i with | 0 => state12_2250 | 1 => state12_2251 | 2 => state12_2252 | 3 => state12_2253 | _ => state12_2254

def stree12RRRRLLLL (i : Nat) : State := if i < 4 then stree12RRRRLLLLL i else stree12RRRRLLLLR (i - 4)

def stree12RRRRLLLRL (i : Nat) : State := match i with | 0 => state12_2255 | 1 => state12_2256 | 2 => state12_2257 | _ => state12_2258

def stree12RRRRLLLRR (i : Nat) : State := match i with | 0 => state12_2259 | 1 => state12_2260 | 2 => state12_2261 | 3 => state12_2262 | _ => state12_2263

def stree12RRRRLLLR (i : Nat) : State := if i < 4 then stree12RRRRLLLRL i else stree12RRRRLLLRR (i - 4)

def stree12RRRRLLL (i : Nat) : State := if i < 9 then stree12RRRRLLLL i else stree12RRRRLLLR (i - 9)

def stree12RRRRLLRLL (i : Nat) : State := match i with | 0 => state12_2264 | 1 => state12_2265 | 2 => state12_2266 | _ => state12_2267

def stree12RRRRLLRLR (i : Nat) : State := match i with | 0 => state12_2268 | 1 => state12_2269 | 2 => state12_2270 | 3 => state12_2271 | _ => state12_2272

def stree12RRRRLLRL (i : Nat) : State := if i < 4 then stree12RRRRLLRLL i else stree12RRRRLLRLR (i - 4)

def stree12RRRRLLRRL (i : Nat) : State := match i with | 0 => state12_2273 | 1 => state12_2274 | 2 => state12_2275 | 3 => state12_2276 | _ => state12_2277

def stree12RRRRLLRRR (i : Nat) : State := match i with | 0 => state12_2278 | 1 => state12_2279 | 2 => state12_2280 | 3 => state12_2281 | _ => state12_2282

def stree12RRRRLLRR (i : Nat) : State := if i < 5 then stree12RRRRLLRRL i else stree12RRRRLLRRR (i - 5)

def stree12RRRRLLR (i : Nat) : State := if i < 9 then stree12RRRRLLRL i else stree12RRRRLLRR (i - 9)

def stree12RRRRLL (i : Nat) : State := if i < 18 then stree12RRRRLLL i else stree12RRRRLLR (i - 18)

def stree12RRRRLRLLL (i : Nat) : State := match i with | 0 => state12_2283 | 1 => state12_2284 | 2 => state12_2285 | _ => state12_2286

def stree12RRRRLRLLR (i : Nat) : State := match i with | 0 => state12_2287 | 1 => state12_2288 | 2 => state12_2289 | 3 => state12_2290 | _ => state12_2291

def stree12RRRRLRLL (i : Nat) : State := if i < 4 then stree12RRRRLRLLL i else stree12RRRRLRLLR (i - 4)

def stree12RRRRLRLRL (i : Nat) : State := match i with | 0 => state12_2292 | 1 => state12_2293 | 2 => state12_2294 | 3 => state12_2295 | _ => state12_2296

def stree12RRRRLRLRR (i : Nat) : State := match i with | 0 => state12_2297 | 1 => state12_2298 | 2 => state12_2299 | 3 => state12_2300 | _ => state12_2301

def stree12RRRRLRLR (i : Nat) : State := if i < 5 then stree12RRRRLRLRL i else stree12RRRRLRLRR (i - 5)

def stree12RRRRLRL (i : Nat) : State := if i < 9 then stree12RRRRLRLL i else stree12RRRRLRLR (i - 9)

def stree12RRRRLRRLL (i : Nat) : State := match i with | 0 => state12_2302 | 1 => state12_2303 | 2 => state12_2304 | _ => state12_2305

def stree12RRRRLRRLR (i : Nat) : State := match i with | 0 => state12_2306 | 1 => state12_2307 | 2 => state12_2308 | 3 => state12_2309 | _ => state12_2310

def stree12RRRRLRRL (i : Nat) : State := if i < 4 then stree12RRRRLRRLL i else stree12RRRRLRRLR (i - 4)

def stree12RRRRLRRRL (i : Nat) : State := match i with | 0 => state12_2311 | 1 => state12_2312 | 2 => state12_2313 | 3 => state12_2314 | _ => state12_2315

def stree12RRRRLRRRR (i : Nat) : State := match i with | 0 => state12_2316 | 1 => state12_2317 | 2 => state12_2318 | 3 => state12_2319 | _ => state12_2320

def stree12RRRRLRRR (i : Nat) : State := if i < 5 then stree12RRRRLRRRL i else stree12RRRRLRRRR (i - 5)

def stree12RRRRLRR (i : Nat) : State := if i < 9 then stree12RRRRLRRL i else stree12RRRRLRRR (i - 9)

def stree12RRRRLR (i : Nat) : State := if i < 19 then stree12RRRRLRL i else stree12RRRRLRR (i - 19)

def stree12RRRRL (i : Nat) : State := if i < 37 then stree12RRRRLL i else stree12RRRRLR (i - 37)

def stree12RRRRRLLLL (i : Nat) : State := match i with | 0 => state12_2321 | 1 => state12_2322 | 2 => state12_2323 | _ => state12_2324

def stree12RRRRRLLLR (i : Nat) : State := match i with | 0 => state12_2325 | 1 => state12_2326 | 2 => state12_2327 | 3 => state12_2328 | _ => state12_2329

def stree12RRRRRLLL (i : Nat) : State := if i < 4 then stree12RRRRRLLLL i else stree12RRRRRLLLR (i - 4)

def stree12RRRRRLLRL (i : Nat) : State := match i with | 0 => state12_2330 | 1 => state12_2331 | 2 => state12_2332 | _ => state12_2333

def stree12RRRRRLLRR (i : Nat) : State := match i with | 0 => state12_2334 | 1 => state12_2335 | 2 => state12_2336 | 3 => state12_2337 | _ => state12_2338

def stree12RRRRRLLR (i : Nat) : State := if i < 4 then stree12RRRRRLLRL i else stree12RRRRRLLRR (i - 4)

def stree12RRRRRLL (i : Nat) : State := if i < 9 then stree12RRRRRLLL i else stree12RRRRRLLR (i - 9)

def stree12RRRRRLRLL (i : Nat) : State := match i with | 0 => state12_2339 | 1 => state12_2340 | 2 => state12_2341 | _ => state12_2342

def stree12RRRRRLRLR (i : Nat) : State := match i with | 0 => state12_2343 | 1 => state12_2344 | 2 => state12_2345 | 3 => state12_2346 | _ => state12_2347

def stree12RRRRRLRL (i : Nat) : State := if i < 4 then stree12RRRRRLRLL i else stree12RRRRRLRLR (i - 4)

def stree12RRRRRLRRL (i : Nat) : State := match i with | 0 => state12_2348 | 1 => state12_2349 | 2 => state12_2350 | 3 => state12_2351 | _ => state12_2352

def stree12RRRRRLRRR (i : Nat) : State := match i with | 0 => state12_2353 | 1 => state12_2354 | 2 => state12_2355 | 3 => state12_2356 | _ => state12_2357

def stree12RRRRRLRR (i : Nat) : State := if i < 5 then stree12RRRRRLRRL i else stree12RRRRRLRRR (i - 5)

def stree12RRRRRLR (i : Nat) : State := if i < 9 then stree12RRRRRLRL i else stree12RRRRRLRR (i - 9)

def stree12RRRRRL (i : Nat) : State := if i < 18 then stree12RRRRRLL i else stree12RRRRRLR (i - 18)

def stree12RRRRRRLLL (i : Nat) : State := match i with | 0 => state12_2358 | 1 => state12_2359 | 2 => state12_2360 | _ => state12_2361

def stree12RRRRRRLLR (i : Nat) : State := match i with | 0 => state12_2362 | 1 => state12_2363 | 2 => state12_2364 | 3 => state12_2365 | _ => state12_2366

def stree12RRRRRRLL (i : Nat) : State := if i < 4 then stree12RRRRRRLLL i else stree12RRRRRRLLR (i - 4)

def stree12RRRRRRLRL (i : Nat) : State := match i with | 0 => state12_2367 | 1 => state12_2368 | 2 => state12_2369 | 3 => state12_2370 | _ => state12_2371

def stree12RRRRRRLRR (i : Nat) : State := match i with | 0 => state12_2372 | 1 => state12_2373 | 2 => state12_2374 | 3 => state12_2375 | _ => state12_2376

def stree12RRRRRRLR (i : Nat) : State := if i < 5 then stree12RRRRRRLRL i else stree12RRRRRRLRR (i - 5)

def stree12RRRRRRL (i : Nat) : State := if i < 9 then stree12RRRRRRLL i else stree12RRRRRRLR (i - 9)

def stree12RRRRRRRLL (i : Nat) : State := match i with | 0 => state12_2377 | 1 => state12_2378 | 2 => state12_2379 | _ => state12_2380

def stree12RRRRRRRLR (i : Nat) : State := match i with | 0 => state12_2381 | 1 => state12_2382 | 2 => state12_2383 | 3 => state12_2384 | _ => state12_2385

def stree12RRRRRRRL (i : Nat) : State := if i < 4 then stree12RRRRRRRLL i else stree12RRRRRRRLR (i - 4)

def stree12RRRRRRRRL (i : Nat) : State := match i with | 0 => state12_2386 | 1 => state12_2387 | 2 => state12_2388 | 3 => state12_2389 | _ => state12_2390

def stree12RRRRRRRRR (i : Nat) : State := match i with | 0 => state12_2391 | 1 => state12_2392 | 2 => state12_2393 | 3 => state12_2394 | _ => state12_2395

def stree12RRRRRRRR (i : Nat) : State := if i < 5 then stree12RRRRRRRRL i else stree12RRRRRRRRR (i - 5)

def stree12RRRRRRR (i : Nat) : State := if i < 9 then stree12RRRRRRRL i else stree12RRRRRRRR (i - 9)

def stree12RRRRRR (i : Nat) : State := if i < 19 then stree12RRRRRRL i else stree12RRRRRRR (i - 19)

def stree12RRRRR (i : Nat) : State := if i < 37 then stree12RRRRRL i else stree12RRRRRR (i - 37)

def stree12RRRR (i : Nat) : State := if i < 75 then stree12RRRRL i else stree12RRRRR (i - 75)

def stree12RRR (i : Nat) : State := if i < 150 then stree12RRRL i else stree12RRRR (i - 150)

def stree12RR (i : Nat) : State := if i < 299 then stree12RRL i else stree12RRR (i - 299)

def stree12R (i : Nat) : State := if i < 599 then stree12RL i else stree12RR (i - 599)

def stree12 (i : Nat) : State := if i < 1198 then stree12L i else stree12R (i - 1198)

def ntree12LLLLLLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 1 => ![⟨2,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨5,by decide⟩,⟨5,by decide⟩] | 3 => ![⟨6,by decide⟩,⟨7,by decide⟩,⟨7,by decide⟩] | 4 => ![⟨8,by decide⟩,⟨9,by decide⟩,⟨1,by decide⟩] | _ => ![⟨10,by decide⟩,⟨11,by decide⟩,⟨3,by decide⟩]

def ntree12LLLLLLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨12,by decide⟩,⟨13,by decide⟩,⟨5,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨15,by decide⟩,⟨7,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨2,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩]

def ntree12LLLLLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLLLLLLL i else ntree12LLLLLLLLR (i - 6)

def ntree12LLLLLLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨12,by decide⟩,⟨12,by decide⟩,⟨4,by decide⟩] | 1 => ![⟨14,by decide⟩,⟨14,by decide⟩,⟨6,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | 3 => ![⟨6,by decide⟩,⟨6,by decide⟩,⟨6,by decide⟩] | 4 => ![⟨16,by decide⟩,⟨17,by decide⟩,⟨1,by decide⟩] | _ => ![⟨18,by decide⟩,⟨19,by decide⟩,⟨5,by decide⟩]

def ntree12LLLLLLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨16,by decide⟩,⟨16,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨18,by decide⟩,⟨18,by decide⟩,⟨4,by decide⟩] | 2 => ![⟨20,by decide⟩,⟨21,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨22,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨23,by decide⟩,⟨0,by decide⟩] | _ => ![⟨22,by decide⟩,⟨23,by decide⟩,⟨0,by decide⟩]

def ntree12LLLLLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLLLLLRL i else ntree12LLLLLLLRR (i - 6)

def ntree12LLLLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLLLLLLL i else ntree12LLLLLLLR (i - 12)

def ntree12LLLLLLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨24,by decide⟩,⟨0,by decide⟩,⟨24,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨25,by decide⟩,⟨25,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨26,by decide⟩,⟨26,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨27,by decide⟩,⟨27,by decide⟩] | 4 => ![⟨16,by decide⟩,⟨28,by decide⟩,⟨27,by decide⟩] | _ => ![⟨29,by decide⟩,⟨16,by decide⟩,⟨24,by decide⟩]

def ntree12LLLLLLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨30,by decide⟩,⟨30,by decide⟩] | 1 => ![⟨2,by decide⟩,⟨31,by decide⟩,⟨31,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨32,by decide⟩,⟨30,by decide⟩] | 3 => ![⟨10,by decide⟩,⟨33,by decide⟩,⟨31,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨34,by decide⟩] | _ => ![⟨20,by decide⟩,⟨20,by decide⟩,⟨0,by decide⟩]

def ntree12LLLLLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLLLLRLL i else ntree12LLLLLLRLR (i - 6)

def ntree12LLLLLLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨35,by decide⟩,⟨30,by decide⟩,⟨36,by decide⟩] | 1 => ![⟨20,by decide⟩,⟨20,by decide⟩,⟨34,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨37,by decide⟩,⟨37,by decide⟩] | 3 => ![⟨38,by decide⟩,⟨39,by decide⟩,⟨39,by decide⟩] | 4 => ![⟨38,by decide⟩,⟨38,by decide⟩,⟨38,by decide⟩] | _ => ![⟨40,by decide⟩,⟨40,by decide⟩,⟨38,by decide⟩]

def ntree12LLLLLLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨35,by decide⟩,⟨0,by decide⟩,⟨35,by decide⟩] | 1 => ![⟨2,by decide⟩,⟨41,by decide⟩,⟨41,by decide⟩] | 2 => ![⟨42,by decide⟩,⟨43,by decide⟩,⟨43,by decide⟩] | 3 => ![⟨44,by decide⟩,⟨45,by decide⟩,⟨45,by decide⟩] | 4 => ![⟨46,by decide⟩,⟨47,by decide⟩,⟨47,by decide⟩] | _ => ![⟨42,by decide⟩,⟨42,by decide⟩,⟨42,by decide⟩]

def ntree12LLLLLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLLLLRRL i else ntree12LLLLLLRRR (i - 6)

def ntree12LLLLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLLLLLRL i else ntree12LLLLLLRR (i - 12)

def ntree12LLLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LLLLLLL i else ntree12LLLLLLR (i - 24)

def ntree12LLLLLRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨44,by decide⟩,⟨44,by decide⟩,⟨44,by decide⟩] | 1 => ![⟨46,by decide⟩,⟨46,by decide⟩,⟨46,by decide⟩] | 2 => ![⟨48,by decide⟩,⟨49,by decide⟩,⟨49,by decide⟩] | 3 => ![⟨48,by decide⟩,⟨48,by decide⟩,⟨48,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨50,by decide⟩,⟨0,by decide⟩] | _ => ![⟨42,by decide⟩,⟨51,by decide⟩,⟨42,by decide⟩]

def ntree12LLLLLRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨52,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨53,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | 2 => ![⟨52,by decide⟩,⟨23,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨54,by decide⟩,⟨42,by decide⟩,⟨42,by decide⟩] | 4 => ![⟨52,by decide⟩,⟨50,by decide⟩,⟨0,by decide⟩] | _ => ![⟨54,by decide⟩,⟨51,by decide⟩,⟨42,by decide⟩]

def ntree12LLLLLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLLLRLLL i else ntree12LLLLLRLLR (i - 6)

def ntree12LLLLLRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨42,by decide⟩,⟨55,by decide⟩,⟨55,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨56,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨57,by decide⟩,⟨58,by decide⟩,⟨30,by decide⟩] | 3 => ![⟨57,by decide⟩,⟨57,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨59,by decide⟩,⟨59,by decide⟩,⟨48,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LLLLLRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨60,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨61,by decide⟩,⟨61,by decide⟩,⟨42,by decide⟩] | 2 => ![⟨62,by decide⟩,⟨62,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨63,by decide⟩,⟨63,by decide⟩,⟨46,by decide⟩] | 4 => ![⟨64,by decide⟩,⟨64,by decide⟩,⟨4,by decide⟩] | _ => ![⟨65,by decide⟩,⟨1,by decide⟩,⟨66,by decide⟩]

def ntree12LLLLLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLLLRLRL i else ntree12LLLLLRLRR (i - 6)

def ntree12LLLLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLLLLRLL i else ntree12LLLLLRLR (i - 12)

def ntree12LLLLLRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨65,by decide⟩,⟨0,by decide⟩,⟨65,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨67,by decide⟩,⟨67,by decide⟩] | 2 => ![⟨68,by decide⟩,⟨42,by decide⟩,⟨68,by decide⟩] | 3 => ![⟨42,by decide⟩,⟨69,by decide⟩,⟨69,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨70,by decide⟩] | _ => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨70,by decide⟩]

def ntree12LLLLLRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨62,by decide⟩,⟨71,by decide⟩,⟨25,by decide⟩] | 1 => ![⟨72,by decide⟩,⟨1,by decide⟩,⟨73,by decide⟩] | 2 => ![⟨74,by decide⟩,⟨3,by decide⟩,⟨75,by decide⟩] | 3 => ![⟨76,by decide⟩,⟨9,by decide⟩,⟨73,by decide⟩] | 4 => ![⟨77,by decide⟩,⟨11,by decide⟩,⟨75,by decide⟩] | _ => ![⟨76,by decide⟩,⟨8,by decide⟩,⟨72,by decide⟩]

def ntree12LLLLLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLLLRRLL i else ntree12LLLLLRRLR (i - 6)

def ntree12LLLLLRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨77,by decide⟩,⟨10,by decide⟩,⟨74,by decide⟩] | 1 => ![⟨72,by decide⟩,⟨0,by decide⟩,⟨72,by decide⟩] | 2 => ![⟨74,by decide⟩,⟨2,by decide⟩,⟨74,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨78,by decide⟩] | 4 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨79,by decide⟩] | _ => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨78,by decide⟩]

def ntree12LLLLLRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨10,by decide⟩,⟨10,by decide⟩,⟨79,by decide⟩] | 1 => ![⟨80,by decide⟩,⟨17,by decide⟩,⟨73,by decide⟩] | 2 => ![⟨80,by decide⟩,⟨16,by decide⟩,⟨72,by decide⟩] | 3 => ![⟨81,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 5 => ![⟨82,by decide⟩,⟨82,by decide⟩,⟨0,by decide⟩] | _ => ![⟨81,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LLLLLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLLLRRRL i else ntree12LLLLLRRRR (i - 6)

def ntree12LLLLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLLLLRRL i else ntree12LLLLLRRR (i - 12)

def ntree12LLLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LLLLLRL i else ntree12LLLLLRR (i - 24)

def ntree12LLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12LLLLLL i else ntree12LLLLLR (i - 48)

def ntree12LLLLRLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨16,by decide⟩,⟨16,by decide⟩,⟨78,by decide⟩] | 1 => ![⟨83,by decide⟩,⟨25,by decide⟩,⟨84,by decide⟩] | 2 => ![⟨83,by decide⟩,⟨0,by decide⟩,⟨83,by decide⟩] | 3 => ![⟨85,by decide⟩,⟨16,by decide⟩,⟨83,by decide⟩] | 4 => ![⟨86,by decide⟩,⟨86,by decide⟩,⟨86,by decide⟩] | _ => ![⟨87,by decide⟩,⟨86,by decide⟩,⟨87,by decide⟩]

def ntree12LLLLRLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨72,by decide⟩,⟨37,by decide⟩,⟨88,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨89,by decide⟩] | 2 => ![⟨90,by decide⟩,⟨90,by decide⟩,⟨86,by decide⟩] | 3 => ![⟨91,by decide⟩,⟨43,by decide⟩,⟨92,by decide⟩] | 4 => ![⟨93,by decide⟩,⟨45,by decide⟩,⟨94,by decide⟩] | _ => ![⟨91,by decide⟩,⟨42,by decide⟩,⟨91,by decide⟩]

def ntree12LLLLRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLLRLLLL i else ntree12LLLLRLLLR (i - 6)

def ntree12LLLLRLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨93,by decide⟩,⟨44,by decide⟩,⟨93,by decide⟩] | 1 => ![⟨95,by decide⟩,⟨49,by decide⟩,⟨96,by decide⟩] | 2 => ![⟨95,by decide⟩,⟨48,by decide⟩,⟨95,by decide⟩] | 3 => ![⟨42,by decide⟩,⟨42,by decide⟩,⟨97,by decide⟩] | 4 => ![⟨44,by decide⟩,⟨44,by decide⟩,⟨98,by decide⟩] | _ => ![⟨0,by decide⟩,⟨99,by decide⟩,⟨0,by decide⟩]

def ntree12LLLLRLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨60,by decide⟩,⟨99,by decide⟩,⟨78,by decide⟩] | 1 => ![⟨81,by decide⟩,⟨99,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨72,by decide⟩,⟨56,by decide⟩,⟨72,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨100,by decide⟩,⟨100,by decide⟩,⟨0,by decide⟩] | _ => ![⟨101,by decide⟩,⟨61,by decide⟩,⟨91,by decide⟩]

def ntree12LLLLRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLLRLLRL i else ntree12LLLLRLLRR (i - 6)

def ntree12LLLLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLLLRLLL i else ntree12LLLLRLLR (i - 12)

def ntree12LLLLRLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨102,by decide⟩,⟨62,by decide⟩,⟨72,by decide⟩] | 1 => ![⟨103,by decide⟩,⟨104,by decide⟩,⟨104,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨105,by decide⟩] | 3 => ![⟨103,by decide⟩,⟨103,by decide⟩,⟨103,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨106,by decide⟩,⟨106,by decide⟩] | _ => ![⟨107,by decide⟩,⟨107,by decide⟩,⟨103,by decide⟩]

def ntree12LLLLRLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨105,by decide⟩] | 1 => ![⟨108,by decide⟩,⟨4,by decide⟩,⟨108,by decide⟩] | 2 => ![⟨109,by decide⟩,⟨0,by decide⟩,⟨109,by decide⟩] | 3 => ![⟨110,by decide⟩,⟨12,by decide⟩,⟨108,by decide⟩] | 4 => ![⟨111,by decide⟩,⟨8,by decide⟩,⟨109,by decide⟩] | _ => ![⟨112,by decide⟩,⟨20,by decide⟩,⟨109,by decide⟩]

def ntree12LLLLRLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLLRLRLL i else ntree12LLLLRLRLR (i - 6)

def ntree12LLLLRLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨113,by decide⟩,⟨113,by decide⟩] | 1 => ![⟨72,by decide⟩,⟨114,by decide⟩,⟨115,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨114,by decide⟩,⟨114,by decide⟩] | 3 => ![⟨116,by decide⟩,⟨38,by decide⟩,⟨116,by decide⟩] | 4 => ![⟨2,by decide⟩,⟨117,by decide⟩,⟨117,by decide⟩] | _ => ![⟨118,by decide⟩,⟨0,by decide⟩,⟨118,by decide⟩]

def ntree12LLLLRLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨119,by decide⟩,⟨46,by decide⟩,⟨119,by decide⟩] | 1 => ![⟨120,by decide⟩,⟨42,by decide⟩,⟨120,by decide⟩] | 2 => ![⟨121,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨122,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨4,by decide⟩,⟨123,by decide⟩,⟨4,by decide⟩] | _ => ![⟨72,by decide⟩,⟨124,by decide⟩,⟨72,by decide⟩]

def ntree12LLLLRLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLLRLRRL i else ntree12LLLLRLRRR (i - 6)

def ntree12LLLLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLLLRLRL i else ntree12LLLLRLRR (i - 12)

def ntree12LLLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LLLLRLL i else ntree12LLLLRLR (i - 24)

def ntree12LLLLRRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨124,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨2,by decide⟩,⟨125,by decide⟩,⟨2,by decide⟩] | 2 => ![⟨126,by decide⟩,⟨63,by decide⟩,⟨119,by decide⟩] | 3 => ![⟨127,by decide⟩,⟨64,by decide⟩,⟨108,by decide⟩] | 4 => ![⟨128,by decide⟩,⟨61,by decide⟩,⟨120,by decide⟩] | _ => ![⟨129,by decide⟩,⟨130,by decide⟩,⟨130,by decide⟩]

def ntree12LLLLRRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨131,by decide⟩,⟨132,by decide⟩,⟨130,by decide⟩] | 1 => ![⟨131,by decide⟩,⟨131,by decide⟩,⟨129,by decide⟩] | 2 => ![⟨129,by decide⟩,⟨129,by decide⟩,⟨129,by decide⟩] | 3 => ![⟨133,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨134,by decide⟩]

def ntree12LLLLRRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLLRRLLL i else ntree12LLLLRRLLR (i - 6)

def ntree12LLLLRRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨133,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨135,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨136,by decide⟩,⟨1,by decide⟩,⟨137,by decide⟩] | 3 => ![⟨138,by decide⟩,⟨139,by decide⟩,⟨1,by decide⟩] | 4 => ![⟨140,by decide⟩,⟨141,by decide⟩,⟨141,by decide⟩] | _ => ![⟨142,by decide⟩,⟨143,by decide⟩,⟨141,by decide⟩]

def ntree12LLLLRRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨144,by decide⟩,⟨144,by decide⟩] | 1 => ![⟨136,by decide⟩,⟨0,by decide⟩,⟨136,by decide⟩] | 2 => ![⟨145,by decide⟩,⟨146,by decide⟩,⟨144,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨147,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨148,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨149,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩]

def ntree12LLLLRRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLLRRLRL i else ntree12LLLLRRLRR (i - 6)

def ntree12LLLLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLLLRRLL i else ntree12LLLLRRLR (i - 12)

def ntree12LLLLRRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨22,by decide⟩,⟨144,by decide⟩,⟨144,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨150,by decide⟩] | 3 => ![⟨149,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨138,by decide⟩,⟨138,by decide⟩,⟨0,by decide⟩] | _ => ![⟨140,by decide⟩,⟨140,by decide⟩,⟨140,by decide⟩]

def ntree12LLLLRRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨142,by decide⟩,⟨142,by decide⟩,⟨140,by decide⟩] | 1 => ![⟨138,by decide⟩,⟨151,by decide⟩,⟨27,by decide⟩] | 2 => ![⟨140,by decide⟩,⟨152,by decide⟩,⟨152,by decide⟩] | 3 => ![⟨145,by decide⟩,⟨145,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨153,by decide⟩,⟨0,by decide⟩] | _ => ![⟨138,by decide⟩,⟨154,by decide⟩,⟨155,by decide⟩]

def ntree12LLLLRRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLLRRRLL i else ntree12LLLLRRRLR (i - 6)

def ntree12LLLLRRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨156,by decide⟩,⟨0,by decide⟩,⟨156,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨157,by decide⟩,⟨144,by decide⟩] | 2 => ![⟨158,by decide⟩,⟨159,by decide⟩,⟨160,by decide⟩] | 3 => ![⟨158,by decide⟩,⟨158,by decide⟩,⟨161,by decide⟩] | 4 => ![⟨162,by decide⟩,⟨8,by decide⟩,⟨156,by decide⟩] | _ => ![⟨149,by decide⟩,⟨153,by decide⟩,⟨34,by decide⟩]

def ntree12LLLLRRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨163,by decide⟩,⟨37,by decide⟩] | 1 => ![⟨138,by decide⟩,⟨164,by decide⟩,⟨37,by decide⟩] | 2 => ![⟨165,by decide⟩,⟨1,by decide⟩,⟨166,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨134,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨167,by decide⟩] | 5 => ![⟨168,by decide⟩,⟨0,by decide⟩,⟨168,by decide⟩] | _ => ![⟨168,by decide⟩,⟨0,by decide⟩,⟨169,by decide⟩]

def ntree12LLLLRRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLLRRRRL i else ntree12LLLLRRRRR (i - 6)

def ntree12LLLLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLLLRRRL i else ntree12LLLLRRRR (i - 12)

def ntree12LLLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LLLLRRL i else ntree12LLLLRRR (i - 24)

def ntree12LLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12LLLLRL i else ntree12LLLLRR (i - 48)

def ntree12LLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 97 then ntree12LLLLL i else ntree12LLLLR (i - 97)

def ntree12LLLRLLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨170,by decide⟩,⟨0,by decide⟩,⟨171,by decide⟩] | 1 => ![⟨172,by decide⟩,⟨173,by decide⟩,⟨43,by decide⟩] | 2 => ![⟨174,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨175,by decide⟩,⟨139,by decide⟩,⟨1,by decide⟩] | 4 => ![⟨42,by decide⟩,⟨176,by decide⟩,⟨42,by decide⟩] | _ => ![⟨177,by decide⟩,⟨42,by decide⟩,⟨42,by decide⟩]

def ntree12LLLRLLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨174,by decide⟩,⟨147,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨174,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨178,by decide⟩,⟨179,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨180,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨181,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨172,by decide⟩,⟨172,by decide⟩,⟨42,by decide⟩]

def ntree12LLLRLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLRLLLLL i else ntree12LLLRLLLLR (i - 6)

def ntree12LLLRLLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨138,by decide⟩,⟨138,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨182,by decide⟩,⟨138,by decide⟩,⟨171,by decide⟩] | 3 => ![⟨52,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨42,by decide⟩,⟨183,by decide⟩,⟨42,by decide⟩] | _ => ![⟨0,by decide⟩,⟨153,by decide⟩,⟨0,by decide⟩]

def ntree12LLLRLLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨175,by decide⟩,⟨138,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨178,by decide⟩,⟨178,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨57,by decide⟩,⟨184,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨185,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨185,by decide⟩,⟨0,by decide⟩,⟨186,by decide⟩]

def ntree12LLLRLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLRLLLRL i else ntree12LLLRLLLRR (i - 6)

def ntree12LLLRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLLRLLLL i else ntree12LLLRLLLR (i - 12)

def ntree12LLLRLLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨187,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨135,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨188,by decide⟩,⟨1,by decide⟩,⟨189,by decide⟩] | 3 => ![⟨190,by decide⟩,⟨43,by decide⟩,⟨191,by decide⟩] | 4 => ![⟨192,by decide⟩,⟨141,by decide⟩,⟨193,by decide⟩] | _ => ![⟨42,by decide⟩,⟨194,by decide⟩,⟨194,by decide⟩]

def ntree12LLLRLLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨188,by decide⟩,⟨144,by decide⟩,⟨195,by decide⟩] | 1 => ![⟨190,by decide⟩,⟨42,by decide⟩,⟨190,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨196,by decide⟩,⟨196,by decide⟩] | 3 => ![⟨188,by decide⟩,⟨0,by decide⟩,⟨188,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨197,by decide⟩,⟨197,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨198,by decide⟩]

def ntree12LLLRLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLRLLRLL i else ntree12LLLRLLRLR (i - 6)

def ntree12LLLRLLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨42,by decide⟩,⟨42,by decide⟩,⟨199,by decide⟩] | 1 => ![⟨140,by decide⟩,⟨140,by decide⟩,⟨200,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨153,by decide⟩,⟨198,by decide⟩] | 3 => ![⟨8,by decide⟩,⟨157,by decide⟩,⟨201,by decide⟩] | 4 => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨198,by decide⟩] | _ => ![⟨61,by decide⟩,⟨202,by decide⟩,⟨194,by decide⟩]

def ntree12LLLRLLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨62,by decide⟩,⟨203,by decide⟩,⟨196,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨204,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨205,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨135,by decide⟩,⟨204,by decide⟩,⟨78,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨206,by decide⟩,⟨0,by decide⟩] | _ => ![⟨8,by decide⟩,⟨207,by decide⟩,⟨208,by decide⟩]

def ntree12LLLRLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLRLLRRL i else ntree12LLLRLLRRR (i - 6)

def ntree12LLLRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLLRLLRL i else ntree12LLLRLLRR (i - 12)

def ntree12LLLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LLLRLLL i else ntree12LLLRLLR (i - 24)

def ntree12LLLRLRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨209,by decide⟩,⟨141,by decide⟩,⟨210,by decide⟩] | 1 => ![⟨72,by decide⟩,⟨144,by decide⟩,⟨211,by decide⟩] | 2 => ![⟨212,by decide⟩,⟨213,by decide⟩,⟨144,by decide⟩] | 3 => ![⟨212,by decide⟩,⟨212,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨214,by decide⟩,⟨212,by decide⟩,⟨72,by decide⟩] | _ => ![⟨215,by decide⟩,⟨141,by decide⟩,⟨141,by decide⟩]

def ntree12LLLRLRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨144,by decide⟩,⟨144,by decide⟩] | 1 => ![⟨140,by decide⟩,⟨140,by decide⟩,⟨216,by decide⟩] | 2 => ![⟨215,by decide⟩,⟨140,by decide⟩,⟨140,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨217,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨208,by decide⟩,⟨208,by decide⟩] | _ => ![⟨72,by decide⟩,⟨153,by decide⟩,⟨72,by decide⟩]

def ntree12LLLRLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLRLRLLL i else ntree12LLLRLRLLR (i - 6)

def ntree12LLLRLRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨218,by decide⟩,⟨219,by decide⟩,⟨218,by decide⟩] | 1 => ![⟨220,by decide⟩,⟨218,by decide⟩,⟨220,by decide⟩] | 2 => ![⟨76,by decide⟩,⟨157,by decide⟩,⟨211,by decide⟩] | 3 => ![⟨221,by decide⟩,⟨222,by decide⟩,⟨223,by decide⟩] | 4 => ![⟨212,by decide⟩,⟨224,by decide⟩,⟨0,by decide⟩] | _ => ![⟨225,by decide⟩,⟨221,by decide⟩,⟨220,by decide⟩]

def ntree12LLLRLRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨153,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨72,by decide⟩,⟨163,by decide⟩,⟨88,by decide⟩] | 2 => ![⟨8,by decide⟩,⟨157,by decide⟩,⟨226,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨218,by decide⟩,⟨218,by decide⟩,⟨218,by decide⟩] | _ => ![⟨8,by decide⟩,⟨8,by decide⟩,⟨217,by decide⟩]

def ntree12LLLRLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLRLRLRL i else ntree12LLLRLRLRR (i - 6)

def ntree12LLLRLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLLRLRLL i else ntree12LLLRLRLR (i - 12)

def ntree12LLLRLRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨37,by decide⟩,⟨37,by decide⟩] | 1 => ![⟨221,by decide⟩,⟨221,by decide⟩,⟨218,by decide⟩] | 2 => ![⟨227,by decide⟩,⟨228,by decide⟩,⟨228,by decide⟩] | 3 => ![⟨229,by decide⟩,⟨228,by decide⟩,⟨230,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨231,by decide⟩,⟨231,by decide⟩] | _ => ![⟨72,by decide⟩,⟨231,by decide⟩,⟨232,by decide⟩]

def ntree12LLLRLRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨233,by decide⟩,⟨231,by decide⟩,⟨234,by decide⟩] | 1 => ![⟨42,by decide⟩,⟨235,by decide⟩,⟨235,by decide⟩] | 2 => ![⟨236,by decide⟩,⟨237,by decide⟩,⟨1,by decide⟩] | 3 => ![⟨238,by decide⟩,⟨237,by decide⟩,⟨73,by decide⟩] | 4 => ![⟨239,by decide⟩,⟨239,by decide⟩,⟨42,by decide⟩] | _ => ![⟨236,by decide⟩,⟨236,by decide⟩,⟨0,by decide⟩]

def ntree12LLLRLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLRLRRLL i else ntree12LLLRLRRLR (i - 6)

def ntree12LLLRLRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨240,by decide⟩,⟨239,by decide⟩,⟨91,by decide⟩] | 1 => ![⟨238,by decide⟩,⟨236,by decide⟩,⟨72,by decide⟩] | 2 => ![⟨241,by decide⟩,⟨228,by decide⟩,⟨228,by decide⟩] | 3 => ![⟨174,by decide⟩,⟨231,by decide⟩,⟨231,by decide⟩] | 4 => ![⟨236,by decide⟩,⟨236,by decide⟩,⟨78,by decide⟩] | _ => ![⟨81,by decide⟩,⟨231,by decide⟩,⟨231,by decide⟩]

def ntree12LLLRLRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨91,by decide⟩,⟨183,by decide⟩,⟨91,by decide⟩] | 1 => ![⟨236,by decide⟩,⟨242,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨239,by decide⟩,⟨243,by decide⟩,⟨42,by decide⟩] | 3 => ![⟨100,by decide⟩,⟨244,by decide⟩,⟨231,by decide⟩] | 4 => ![⟨42,by decide⟩,⟨42,by decide⟩,⟨42,by decide⟩] | 5 => ![⟨245,by decide⟩,⟨246,by decide⟩,⟨1,by decide⟩] | _ => ![⟨247,by decide⟩,⟨248,by decide⟩,⟨228,by decide⟩]

def ntree12LLLRLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLRLRRRL i else ntree12LLLRLRRRR (i - 6)

def ntree12LLLRLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLLRLRRL i else ntree12LLLRLRRR (i - 12)

def ntree12LLLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LLLRLRL i else ntree12LLLRLRR (i - 24)

def ntree12LLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12LLLRLL i else ntree12LLLRLR (i - 48)

def ntree12LLLRRLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨8,by decide⟩,⟨249,by decide⟩,⟨231,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨250,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨251,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨42,by decide⟩,⟨252,by decide⟩,⟨42,by decide⟩] | 4 => ![⟨253,by decide⟩,⟨250,by decide⟩,⟨78,by decide⟩] | _ => ![⟨62,by decide⟩,⟨254,by decide⟩,⟨231,by decide⟩]

def ntree12LLLRRLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨61,by decide⟩,⟨255,by decide⟩,⟨235,by decide⟩] | 1 => ![⟨91,by decide⟩,⟨194,by decide⟩,⟨256,by decide⟩] | 2 => ![⟨72,by decide⟩,⟨196,by decide⟩,⟨257,by decide⟩] | 3 => ![⟨258,by decide⟩,⟨259,by decide⟩,⟨259,by decide⟩] | 4 => ![⟨103,by decide⟩,⟨260,by decide⟩,⟨260,by decide⟩] | _ => ![⟨140,by decide⟩,⟨261,by decide⟩,⟨261,by decide⟩]

def ntree12LLLRRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLRRLLLL i else ntree12LLLRRLLLR (i - 6)

def ntree12LLLRRLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨42,by decide⟩,⟨42,by decide⟩,⟨262,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨263,by decide⟩] | 2 => ![⟨101,by decide⟩,⟨202,by decide⟩,⟨256,by decide⟩] | 3 => ![⟨102,by decide⟩,⟨203,by decide⟩,⟨257,by decide⟩] | 4 => ![⟨103,by decide⟩,⟨264,by decide⟩,⟨103,by decide⟩] | _ => ![⟨107,by decide⟩,⟨265,by decide⟩,⟨260,by decide⟩]

def ntree12LLLRRLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨61,by decide⟩,⟨61,by decide⟩,⟨262,by decide⟩] | 1 => ![⟨62,by decide⟩,⟨62,by decide⟩,⟨263,by decide⟩] | 2 => ![⟨72,by decide⟩,⟨266,by decide⟩,⟨72,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨266,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨267,by decide⟩,⟨0,by decide⟩] | _ => ![⟨72,by decide⟩,⟨268,by decide⟩,⟨269,by decide⟩]

def ntree12LLLRRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLRRLLRL i else ntree12LLLRRLLRR (i - 6)

def ntree12LLLRRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLLRRLLL i else ntree12LLLRRLLR (i - 12)

def ntree12LLLRRLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨268,by decide⟩,⟨268,by decide⟩] | 1 => ![⟨138,by decide⟩,⟨270,by decide⟩,⟨268,by decide⟩] | 2 => ![⟨271,by decide⟩,⟨138,by decide⟩,⟨72,by decide⟩] | 3 => ![⟨272,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨209,by decide⟩,⟨140,by decide⟩,⟨209,by decide⟩] | _ => ![⟨72,by decide⟩,⟨273,by decide⟩,⟨72,by decide⟩]

def ntree12LLLRRLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨273,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨274,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨274,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨275,by decide⟩,⟨0,by decide⟩]

def ntree12LLLRRLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLRRLRLL i else ntree12LLLRRLRLR (i - 6)

def ntree12LLLRRLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨276,by decide⟩,⟨158,by decide⟩,⟨277,by decide⟩] | 1 => ![⟨278,by decide⟩,⟨8,by decide⟩,⟨279,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨268,by decide⟩,⟨280,by decide⟩] | 3 => ![⟨138,by decide⟩,⟨281,by decide⟩,⟨114,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨282,by decide⟩,⟨282,by decide⟩] | _ => ![⟨0,by decide⟩,⟨283,by decide⟩,⟨283,by decide⟩]

def ntree12LLLRRLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨284,by decide⟩,⟨284,by decide⟩] | 1 => ![⟨129,by decide⟩,⟨285,by decide⟩,⟨285,by decide⟩] | 2 => ![⟨286,by decide⟩,⟨172,by decide⟩,⟨91,by decide⟩] | 3 => ![⟨287,by decide⟩,⟨42,by decide⟩,⟨42,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨288,by decide⟩,⟨0,by decide⟩] | _ => ![⟨138,by decide⟩,⟨289,by decide⟩,⟨0,by decide⟩]

def ntree12LLLRRLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLRRLRRL i else ntree12LLLRRLRRR (i - 6)

def ntree12LLLRRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLLRRLRL i else ntree12LLLRRLRR (i - 12)

def ntree12LLLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LLLRRLL i else ntree12LLLRRLR (i - 24)

def ntree12LLLRRRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨72,by decide⟩,⟨288,by decide⟩,⟨72,by decide⟩] | 1 => ![⟨271,by decide⟩,⟨289,by decide⟩,⟨72,by decide⟩] | 2 => ![⟨272,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨290,by decide⟩,⟨178,by decide⟩,⟨72,by decide⟩] | 4 => ![⟨291,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | _ => ![⟨138,by decide⟩,⟨292,by decide⟩,⟨231,by decide⟩]

def ntree12LLLRRRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨72,by decide⟩,⟨293,by decide⟩,⟨72,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨293,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨138,by decide⟩,⟨294,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨72,by decide⟩,⟨295,by decide⟩,⟨296,by decide⟩] | 4 => ![⟨91,by decide⟩,⟨297,by decide⟩,⟨298,by decide⟩] | _ => ![⟨0,by decide⟩,⟨295,by decide⟩,⟨295,by decide⟩]

def ntree12LLLRRRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLRRRLLL i else ntree12LLLRRRLLR (i - 6)

def ntree12LLLRRRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨42,by decide⟩,⟨297,by decide⟩,⟨297,by decide⟩] | 1 => ![⟨209,by decide⟩,⟨299,by decide⟩,⟨300,by decide⟩] | 2 => ![⟨140,by decide⟩,⟨299,by decide⟩,⟨299,by decide⟩] | 3 => ![⟨76,by decide⟩,⟨301,by decide⟩,⟨296,by decide⟩] | 4 => ![⟨8,by decide⟩,⟨301,by decide⟩,⟨295,by decide⟩] | _ => ![⟨57,by decide⟩,⟨302,by decide⟩,⟨268,by decide⟩]

def ntree12LLLRRRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨303,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨2,by decide⟩,⟨304,by decide⟩,⟨2,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨305,by decide⟩,⟨4,by decide⟩] | 3 => ![⟨6,by decide⟩,⟨306,by decide⟩,⟨6,by decide⟩] | 4 => ![⟨307,by decide⟩,⟨307,by decide⟩,⟨0,by decide⟩] | _ => ![⟨308,by decide⟩,⟨308,by decide⟩,⟨4,by decide⟩]

def ntree12LLLRRRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLRRRLRL i else ntree12LLLRRRLRR (i - 6)

def ntree12LLLRRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLLRRRLL i else ntree12LLLRRRLR (i - 12)

def ntree12LLLRRRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨307,by decide⟩,⟨309,by decide⟩,⟨144,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨310,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨311,by decide⟩,⟨311,by decide⟩] | 3 => ![⟨308,by decide⟩,⟨312,by decide⟩,⟨311,by decide⟩] | 4 => ![⟨138,by decide⟩,⟨313,by decide⟩,⟨314,by decide⟩] | _ => ![⟨315,by decide⟩,⟨144,by decide⟩,⟨144,by decide⟩]

def ntree12LLLRRRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨315,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨314,by decide⟩,⟨314,by decide⟩] | 2 => ![⟨316,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨317,by decide⟩,⟨144,by decide⟩] | 4 => ![⟨307,by decide⟩,⟨318,by decide⟩,⟨0,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨319,by decide⟩]

def ntree12LLLRRRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLRRRRLL i else ntree12LLLRRRRLR (i - 6)

def ntree12LLLRRRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨320,by decide⟩] | 1 => ![⟨321,by decide⟩,⟨321,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨322,by decide⟩,⟨322,by decide⟩,⟨2,by decide⟩] | 3 => ![⟨138,by decide⟩,⟨138,by decide⟩,⟨319,by decide⟩] | 4 => ![⟨2,by decide⟩,⟨323,by decide⟩,⟨323,by decide⟩] | _ => ![⟨321,by decide⟩,⟨324,by decide⟩,⟨144,by decide⟩]

def ntree12LLLRRRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨322,by decide⟩,⟨325,by decide⟩,⟨323,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨326,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨138,by decide⟩,⟨327,by decide⟩,⟨328,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨328,by decide⟩,⟨328,by decide⟩] | 4 => ![⟨329,by decide⟩,⟨329,by decide⟩,⟨38,by decide⟩] | 5 => ![⟨38,by decide⟩,⟨330,by decide⟩,⟨330,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨331,by decide⟩]

def ntree12LLLRRRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLLRRRRRL i else ntree12LLLRRRRRR (i - 6)

def ntree12LLLRRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLLRRRRL i else ntree12LLLRRRRR (i - 12)

def ntree12LLLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LLLRRRL i else ntree12LLLRRRR (i - 24)

def ntree12LLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12LLLRRL i else ntree12LLLRRR (i - 48)

def ntree12LLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 97 then ntree12LLLRL i else ntree12LLLRR (i - 97)

def ntree12LLL (i : Nat) : Fin 3 → Fin 2396 := if i < 194 then ntree12LLLL i else ntree12LLLR (i - 194)

def ntree12LLRLLLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨332,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨4,by decide⟩,⟨333,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨334,by decide⟩] | 3 => ![⟨335,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨336,by decide⟩,⟨307,by decide⟩,⟨0,by decide⟩] | _ => ![⟨337,by decide⟩,⟨4,by decide⟩,⟨4,by decide⟩]

def ntree12LLRLLLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨338,by decide⟩,⟨308,by decide⟩,⟨4,by decide⟩] | 1 => ![⟨339,by decide⟩,⟨138,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨340,by decide⟩,⟨307,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨341,by decide⟩,⟨42,by decide⟩,⟨42,by decide⟩] | 4 => ![⟨342,by decide⟩,⟨46,by decide⟩,⟨46,by decide⟩] | _ => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨332,by decide⟩]

def ntree12LLRLLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRLLLLLL i else ntree12LLRLLLLLR (i - 6)

def ntree12LLRLLLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨174,by decide⟩,⟨23,by decide⟩,⟨334,by decide⟩] | 1 => ![⟨138,by decide⟩,⟨343,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨344,by decide⟩,⟨344,by decide⟩,⟨42,by decide⟩] | 3 => ![⟨345,by decide⟩,⟨345,by decide⟩,⟨44,by decide⟩] | 4 => ![⟨346,by decide⟩,⟨346,by decide⟩,⟨48,by decide⟩] | _ => ![⟨321,by decide⟩,⟨347,by decide⟩,⟨0,by decide⟩]

def ntree12LLRLLLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨348,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨348,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨348,by decide⟩,⟨303,by decide⟩,⟨332,by decide⟩] | 3 => ![⟨349,by decide⟩,⟨303,by decide⟩,⟨334,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨144,by decide⟩,⟨201,by decide⟩] | _ => ![⟨46,by decide⟩,⟨350,by decide⟩,⟨350,by decide⟩]

def ntree12LLRLLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRLLLLRL i else ntree12LLRLLLLRR (i - 6)

def ntree12LLRLLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLRLLLLL i else ntree12LLRLLLLR (i - 12)

def ntree12LLRLLLRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨42,by decide⟩,⟨351,by decide⟩,⟨351,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨352,by decide⟩,⟨352,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨353,by decide⟩,⟨353,by decide⟩] | 3 => ![⟨65,by decide⟩,⟨144,by decide⟩,⟨354,by decide⟩] | 4 => ![⟨24,by decide⟩,⟨0,by decide⟩,⟨355,by decide⟩] | _ => ![⟨356,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]

def ntree12LLRLLLRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨356,by decide⟩,⟨144,by decide⟩,⟨144,by decide⟩] | 1 => ![⟨357,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 2 => ![⟨358,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨72,by decide⟩,⟨303,by decide⟩,⟨72,by decide⟩] | 4 => ![⟨74,by decide⟩,⟨304,by decide⟩,⟨74,by decide⟩] | _ => ![⟨359,by decide⟩,⟨359,by decide⟩,⟨0,by decide⟩]

def ntree12LLRLLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRLLLRLL i else ntree12LLRLLLRLR (i - 6)

def ntree12LLRLLLRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨359,by decide⟩,⟨360,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨0,by decide⟩,⟨361,by decide⟩,⟨361,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨362,by decide⟩,⟨362,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩] | _ => ![⟨0,by decide⟩,⟨363,by decide⟩,⟨363,by decide⟩]

def ntree12LLRLLLRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨2,by decide⟩,⟨364,by decide⟩,⟨364,by decide⟩] | 1 => ![⟨365,by decide⟩,⟨307,by decide⟩,⟨72,by decide⟩] | 2 => ![⟨365,by decide⟩,⟨309,by decide⟩,⟨211,by decide⟩] | 3 => ![⟨72,by decide⟩,⟨310,by decide⟩,⟨72,by decide⟩] | 4 => ![⟨366,by decide⟩,⟨366,by decide⟩,⟨0,by decide⟩] | _ => ![⟨367,by decide⟩,⟨367,by decide⟩,⟨0,by decide⟩]

def ntree12LLRLLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRLLLRRL i else ntree12LLRLLLRRR (i - 6)

def ntree12LLRLLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLRLLLRL i else ntree12LLRLLLRR (i - 12)

def ntree12LLRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LLRLLLL i else ntree12LLRLLLR (i - 24)

def ntree12LLRLLRLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨368,by decide⟩,⟨0,by decide⟩] | 1 => ![⟨307,by decide⟩,⟨307,by decide⟩,⟨217,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩] | 3 => ![⟨369,by decide⟩,⟨307,by decide⟩,⟨83,by decide⟩] | 4 => ![⟨74,by decide⟩,⟨323,by decide⟩,⟨370,by decide⟩] | _ => ![⟨72,by decide⟩,⟨328,by decide⟩,⟨371,by decide⟩]

def ntree12LLRLLRLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨86,by decide⟩,⟨372,by decide⟩,⟨372,by decide⟩] | 1 => ![⟨2,by decide⟩,⟨2,by decide⟩,⟨373,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨374,by decide⟩] | 3 => ![⟨375,by decide⟩,⟨212,by decide⟩,⟨35,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨376,by decide⟩,⟨376,by decide⟩] | _ => ![⟨48,by decide⟩,⟨377,by decide⟩,⟨377,by decide⟩]

def ntree12LLRLLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRLLRLLL i else ntree12LLRLLRLLR (i - 6)

def ntree12LLRLLRLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨378,by decide⟩,⟨378,by decide⟩] | 1 => ![⟨2,by decide⟩,⟨379,by decide⟩,⟨379,by decide⟩] | 2 => ![⟨42,by decide⟩,⟨380,by decide⟩,⟨380,by decide⟩] | 3 => ![⟨44,by decide⟩,⟨381,by decide⟩,⟨381,by decide⟩] | 4 => ![⟨382,by decide⟩,⟨382,by decide⟩,⟨0,by decide⟩] | _ => ![⟨383,by decide⟩,⟨382,by decide⟩,⟨72,by decide⟩]

def ntree12LLRLLRLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨307,by decide⟩,⟨384,by decide⟩,⟨231,by decide⟩] | 1 => ![⟨385,by decide⟩,⟨385,by decide⟩,⟨2,by decide⟩] | 2 => ![⟨212,by decide⟩,⟨386,by decide⟩,⟨378,by decide⟩] | 3 => ![⟨387,by decide⟩,⟨388,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨389,by decide⟩,⟨390,by decide⟩,⟨231,by decide⟩] | _ => ![⟨0,by decide⟩,⟨391,by decide⟩,⟨391,by decide⟩]

def ntree12LLRLLRLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRLLRLRL i else ntree12LLRLLRLRR (i - 6)

def ntree12LLRLLRL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLRLLRLL i else ntree12LLRLLRLR (i - 12)

def ntree12LLRLLRRLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨392,by decide⟩,⟨392,by decide⟩] | 1 => ![⟨393,by decide⟩,⟨394,by decide⟩,⟨144,by decide⟩] | 2 => ![⟨0,by decide⟩,⟨144,by decide⟩,⟨144,by decide⟩] | 3 => ![⟨393,by decide⟩,⟨393,by decide⟩,⟨0,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨56,by decide⟩,⟨263,by decide⟩] | _ => ![⟨395,by decide⟩,⟨308,by decide⟩,⟨108,by decide⟩]

def ntree12LLRLLRRLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨396,by decide⟩,⟨307,by decide⟩,⟨109,by decide⟩] | 1 => ![⟨72,by decide⟩,⟨397,by decide⟩,⟨398,by decide⟩] | 2 => ![⟨74,by decide⟩,⟨399,by decide⟩,⟨400,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨397,by decide⟩,⟨397,by decide⟩] | 4 => ![⟨2,by decide⟩,⟨399,by decide⟩,⟨399,by decide⟩] | _ => ![⟨321,by decide⟩,⟨401,by decide⟩,⟨397,by decide⟩]

def ntree12LLRLLRRL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRLLRRLL i else ntree12LLRLLRRLR (i - 6)

def ntree12LLRLLRRRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨322,by decide⟩,⟨402,by decide⟩,⟨399,by decide⟩] | 1 => ![⟨271,by decide⟩,⟨403,by decide⟩,⟨398,by decide⟩] | 2 => ![⟨272,by decide⟩,⟨397,by decide⟩,⟨397,by decide⟩] | 3 => ![⟨321,by decide⟩,⟨404,by decide⟩,⟨268,by decide⟩] | 4 => ![⟨405,by decide⟩,⟨138,by decide⟩,⟨118,by decide⟩] | _ => ![⟨72,by decide⟩,⟨406,by decide⟩,⟨407,by decide⟩]

def ntree12LLRLLRRRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨408,by decide⟩] | 1 => ![⟨4,by decide⟩,⟨409,by decide⟩,⟨409,by decide⟩] | 2 => ![⟨108,by decide⟩,⟨409,by decide⟩,⟨410,by decide⟩] | 3 => ![⟨109,by decide⟩,⟨231,by decide⟩,⟨411,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨0,by decide⟩,⟨412,by decide⟩] | 5 => ![⟨0,by decide⟩,⟨413,by decide⟩,⟨413,by decide⟩] | _ => ![⟨2,by decide⟩,⟨414,by decide⟩,⟨414,by decide⟩]

def ntree12LLRLLRRR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRLLRRRL i else ntree12LLRLLRRRR (i - 6)

def ntree12LLRLLRR (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLRLLRRL i else ntree12LLRLLRRR (i - 12)

def ntree12LLRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 24 then ntree12LLRLLRL i else ntree12LLRLLRR (i - 24)

def ntree12LLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 48 then ntree12LLRLLL i else ntree12LLRLLR (i - 48)

def ntree12LLRLRLLLL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨4,by decide⟩,⟨415,by decide⟩,⟨415,by decide⟩] | 1 => ![⟨6,by decide⟩,⟨416,by decide⟩,⟨416,by decide⟩] | 2 => ![⟨307,by decide⟩,⟨417,by decide⟩,⟨406,by decide⟩] | 3 => ![⟨308,by decide⟩,⟨418,by decide⟩,⟨409,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨406,by decide⟩,⟨406,by decide⟩] | _ => ![⟨321,by decide⟩,⟨419,by decide⟩,⟨231,by decide⟩]

def ntree12LLRLRLLLR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨321,by decide⟩,⟨420,by decide⟩,⟨378,by decide⟩] | 1 => ![⟨322,by decide⟩,⟨421,by decide⟩,⟨379,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨422,by decide⟩,⟨422,by decide⟩] | 3 => ![⟨83,by decide⟩,⟨406,by decide⟩,⟨423,by decide⟩] | 4 => ![⟨321,by decide⟩,⟨424,by decide⟩,⟨295,by decide⟩] | _ => ![⟨344,by decide⟩,⟨425,by decide⟩,⟨297,by decide⟩]

def ntree12LLRLRLLL (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRLRLLLL i else ntree12LLRLRLLLR (i - 6)

def ntree12LLRLRLLRL (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨0,by decide⟩,⟨124,by decide⟩,⟨198,by decide⟩] | 1 => ![⟨426,by decide⟩,⟨427,by decide⟩,⟨1,by decide⟩] | 2 => ![⟨428,by decide⟩,⟨429,by decide⟩,⟨5,by decide⟩] | 3 => ![⟨430,by decide⟩,⟨431,by decide⟩,⟨1,by decide⟩] | 4 => ![⟨8,by decide⟩,⟨432,by decide⟩,⟨433,by decide⟩] | _ => ![⟨0,by decide⟩,⟨433,by decide⟩,⟨433,by decide⟩]

def ntree12LLRLRLLRR (i : Nat) : Fin 3 → Fin 2396 := match i with | 0 => ![⟨12,by decide⟩,⟨434,by decide⟩,⟨435,by decide⟩] | 1 => ![⟨8,by decide⟩,⟨436,by decide⟩,⟨437,by decide⟩] | 2 => ![⟨4,by decide⟩,⟨435,by decide⟩,⟨435,by decide⟩] | 3 => ![⟨0,by decide⟩,⟨437,by decide⟩,⟨437,by decide⟩] | 4 => ![⟨0,by decide⟩,⟨438,by decide⟩,⟨0,by decide⟩] | _ => ![⟨439,by decide⟩,⟨0,by decide⟩,⟨439,by decide⟩]

def ntree12LLRLRLLR (i : Nat) : Fin 3 → Fin 2396 := if i < 6 then ntree12LLRLRLLRL i else ntree12LLRLRLLRR (i - 6)

def ntree12LLRLRLL (i : Nat) : Fin 3 → Fin 2396 := if i < 12 then ntree12LLRLRLLL i else ntree12LLRLRLLR (i - 12)

end Paper2.Certificates.Q6.Coverage
