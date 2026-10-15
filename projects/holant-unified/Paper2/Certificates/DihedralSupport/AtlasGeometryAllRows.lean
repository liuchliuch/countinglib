import Paper2.Certificates.DihedralSupport.AtlasGeometryBenchmark
import Paper2.Certificates.DihedralSupport.AtlasGeometryRows000
import Paper2.Certificates.DihedralSupport.AtlasGeometryRows001
import Paper2.Certificates.DihedralSupport.AtlasGeometryRows002
import Paper2.Certificates.DihedralSupport.AtlasGeometryRows003
import Paper2.Certificates.DihedralSupport.AtlasGeometryRows004
import Paper2.Certificates.DihedralSupport.AtlasGeometryRows005
import Paper2.Certificates.DihedralSupport.AtlasGeometryRows006
import Paper2.Certificates.DihedralSupport.AtlasGeometryRows007

namespace Paper2.Certificates.DihedralSupport.AtlasGeometryCheck

theorem all_rows_checked (i : Fin 66) : checkRow i.val = true := by
  fin_cases i
  · exact row_checked_0
  · exact row_checked_1
  · exact row_checked_2
  · exact row_checked_3
  · exact row_checked_4
  · exact row_checked_5
  · exact row_checked_6
  · exact row_checked_7
  · exact row_checked_8
  · exact row_checked_9
  · exact row_checked_10
  · exact row_checked_11
  · exact row_checked_12
  · exact row_checked_13
  · exact row_checked_14
  · exact row_checked_15
  · exact row_checked_16
  · exact row_checked_17
  · exact row_checked_18
  · exact row_checked_19
  · exact row_checked_20
  · exact row_checked_21
  · exact row_checked_22
  · exact row_checked_23
  · exact row_checked_24
  · exact row_checked_25
  · exact row_checked_26
  · exact row_checked_27
  · exact row_checked_28
  · exact row_checked_29
  · exact row_checked_30
  · exact row_checked_31
  · exact row_checked_32
  · exact row_checked_33
  · exact row_checked_34
  · exact row_checked_35
  · exact row_checked_36
  · exact row_checked_37
  · exact row_checked_38
  · exact row_checked_39
  · exact row_checked_40
  · exact row_checked_41
  · exact row_checked_42
  · exact row_checked_43
  · exact row_checked_44
  · exact row_checked_45
  · exact row_checked_46
  · exact row_checked_47
  · exact row_checked_48
  · exact row_checked_49
  · exact row_checked_50
  · exact row_checked_51
  · exact row_checked_52
  · exact row_checked_53
  · exact row_checked_54
  · exact row_checked_55
  · exact row_checked_56
  · exact row_checked_57
  · exact row_checked_58
  · exact row_checked_59
  · exact row_checked_60
  · exact row_checked_61
  · exact row_checked_62
  · exact row_checked_63
  · exact row_checked_64
  · exact row_checked_65

end Paper2.Certificates.DihedralSupport.AtlasGeometryCheck

