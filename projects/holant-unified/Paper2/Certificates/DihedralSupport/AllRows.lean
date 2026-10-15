module
public import Paper2.Certificates.DihedralSupport.Check000
public import Paper2.Certificates.DihedralSupport.Check001
public import Paper2.Certificates.DihedralSupport.Check002
public import Paper2.Certificates.DihedralSupport.Check003
public import Paper2.Certificates.DihedralSupport.Check004
public import Paper2.Certificates.DihedralSupport.Check005
public import Paper2.Certificates.DihedralSupport.Check006
public import Paper2.Certificates.DihedralSupport.Check007
public import Paper2.Certificates.DihedralSupport.Check008
public import Paper2.Certificates.DihedralSupport.Check009
public import Paper2.Certificates.DihedralSupport.Check010
public import Paper2.Certificates.DihedralSupport.Check011
public import Paper2.Certificates.DihedralSupport.Check012
public import Paper2.Certificates.DihedralSupport.Check013
public import Paper2.Certificates.DihedralSupport.Check014
public import Paper2.Certificates.DihedralSupport.Check015
public import Paper2.Certificates.DihedralSupport.Check016
public import Paper2.Certificates.DihedralSupport.Check017
public import Paper2.Certificates.DihedralSupport.Check018
public import Paper2.Certificates.DihedralSupport.Check019
public import Paper2.Certificates.DihedralSupport.Check020
public import Paper2.Certificates.DihedralSupport.Check021
public import Paper2.Certificates.DihedralSupport.Check022
public import Paper2.Certificates.DihedralSupport.Check023
public import Paper2.Certificates.DihedralSupport.Check024
public import Paper2.Certificates.DihedralSupport.Check025
public import Paper2.Certificates.DihedralSupport.Check026
public import Paper2.Certificates.DihedralSupport.Check027
public import Paper2.Certificates.DihedralSupport.Check028
public import Paper2.Certificates.DihedralSupport.Check029
public import Paper2.Certificates.DihedralSupport.Check030
public import Paper2.Certificates.DihedralSupport.Check031
public import Paper2.Certificates.DihedralSupport.Check032
public import Paper2.Certificates.DihedralSupport.Check033
public import Paper2.Certificates.DihedralSupport.Check034
public import Paper2.Certificates.DihedralSupport.Check035
public import Paper2.Certificates.DihedralSupport.Check036
public import Paper2.Certificates.DihedralSupport.Check037
public import Paper2.Certificates.DihedralSupport.Check038
public import Paper2.Certificates.DihedralSupport.Check039
public import Paper2.Certificates.DihedralSupport.Check040
public import Paper2.Certificates.DihedralSupport.Check041
public import Paper2.Certificates.DihedralSupport.Check042
public import Paper2.Certificates.DihedralSupport.Check043
public import Paper2.Certificates.DihedralSupport.Check044
public import Paper2.Certificates.DihedralSupport.Check045
public import Paper2.Certificates.DihedralSupport.Check046
public import Paper2.Certificates.DihedralSupport.Check047
public import Paper2.Certificates.DihedralSupport.Check048
public import Paper2.Certificates.DihedralSupport.Check049
public import Paper2.Certificates.DihedralSupport.Check050
public import Paper2.Certificates.DihedralSupport.Check051
public import Paper2.Certificates.DihedralSupport.Check052
public import Paper2.Certificates.DihedralSupport.Check053
public import Paper2.Certificates.DihedralSupport.Check054
public import Paper2.Certificates.DihedralSupport.Check055
public import Paper2.Certificates.DihedralSupport.Check056
public import Paper2.Certificates.DihedralSupport.Check057
public import Paper2.Certificates.DihedralSupport.Check058
public import Paper2.Certificates.DihedralSupport.Check059
public import Paper2.Certificates.DihedralSupport.Check060
public import Paper2.Certificates.DihedralSupport.Check061
public import Paper2.Certificates.DihedralSupport.Check062
public import Paper2.Certificates.DihedralSupport.Check063
public import Paper2.Certificates.DihedralSupport.Check064
public import Paper2.Certificates.DihedralSupport.Check065

@[expose] public section
namespace Paper2.Certificates.DihedralSupport

private theorem checkRange_append (f : Nat → Bool) (start m n : Nat) :
    checkRange f start (m+n) = (checkRange f start m && checkRange f (start+m) n) := by
  induction n with
  | zero => simp only [Nat.add_zero,checkRange,Bool.and_true]
  | succ n ih =>
    change (checkRange f start (m+n) && f (start+(m+n))) =
      (checkRange f start m && (checkRange f (start+m) n && f ((start+m)+n)))
    rw [ih]
    simp only [Nat.add_assoc,Bool.and_assoc]

private theorem join_checked {f : Nat → Bool} {m n : Nat}
    (hm : checkRange f 0 m = true) (hn : checkRange f m n = true) :
    checkRange f 0 (m+n) = true := by
  rw [checkRange_append]
  rw [Nat.zero_add,hm,hn]
  rfl

/-- Every candidate row is checked by an actual kernel proof. -/
theorem all_ranges_checked : checkRange rowCheck 0 1045 = true := by
  have h0 : checkRange rowCheck 0 16 = true := range_checked_0
  have h1 : checkRange rowCheck 0 32 = true := by
    simpa only [Nat.reduceAdd] using join_checked h0 range_checked_1
  have h2 : checkRange rowCheck 0 48 = true := by
    simpa only [Nat.reduceAdd] using join_checked h1 range_checked_2
  have h3 : checkRange rowCheck 0 64 = true := by
    simpa only [Nat.reduceAdd] using join_checked h2 range_checked_3
  have h4 : checkRange rowCheck 0 80 = true := by
    simpa only [Nat.reduceAdd] using join_checked h3 range_checked_4
  have h5 : checkRange rowCheck 0 96 = true := by
    simpa only [Nat.reduceAdd] using join_checked h4 range_checked_5
  have h6 : checkRange rowCheck 0 112 = true := by
    simpa only [Nat.reduceAdd] using join_checked h5 range_checked_6
  have h7 : checkRange rowCheck 0 128 = true := by
    simpa only [Nat.reduceAdd] using join_checked h6 range_checked_7
  have h8 : checkRange rowCheck 0 144 = true := by
    simpa only [Nat.reduceAdd] using join_checked h7 range_checked_8
  have h9 : checkRange rowCheck 0 160 = true := by
    simpa only [Nat.reduceAdd] using join_checked h8 range_checked_9
  have h10 : checkRange rowCheck 0 176 = true := by
    simpa only [Nat.reduceAdd] using join_checked h9 range_checked_10
  have h11 : checkRange rowCheck 0 192 = true := by
    simpa only [Nat.reduceAdd] using join_checked h10 range_checked_11
  have h12 : checkRange rowCheck 0 208 = true := by
    simpa only [Nat.reduceAdd] using join_checked h11 range_checked_12
  have h13 : checkRange rowCheck 0 224 = true := by
    simpa only [Nat.reduceAdd] using join_checked h12 range_checked_13
  have h14 : checkRange rowCheck 0 240 = true := by
    simpa only [Nat.reduceAdd] using join_checked h13 range_checked_14
  have h15 : checkRange rowCheck 0 256 = true := by
    simpa only [Nat.reduceAdd] using join_checked h14 range_checked_15
  have h16 : checkRange rowCheck 0 272 = true := by
    simpa only [Nat.reduceAdd] using join_checked h15 range_checked_16
  have h17 : checkRange rowCheck 0 288 = true := by
    simpa only [Nat.reduceAdd] using join_checked h16 range_checked_17
  have h18 : checkRange rowCheck 0 304 = true := by
    simpa only [Nat.reduceAdd] using join_checked h17 range_checked_18
  have h19 : checkRange rowCheck 0 320 = true := by
    simpa only [Nat.reduceAdd] using join_checked h18 range_checked_19
  have h20 : checkRange rowCheck 0 336 = true := by
    simpa only [Nat.reduceAdd] using join_checked h19 range_checked_20
  have h21 : checkRange rowCheck 0 352 = true := by
    simpa only [Nat.reduceAdd] using join_checked h20 range_checked_21
  have h22 : checkRange rowCheck 0 368 = true := by
    simpa only [Nat.reduceAdd] using join_checked h21 range_checked_22
  have h23 : checkRange rowCheck 0 384 = true := by
    simpa only [Nat.reduceAdd] using join_checked h22 range_checked_23
  have h24 : checkRange rowCheck 0 400 = true := by
    simpa only [Nat.reduceAdd] using join_checked h23 range_checked_24
  have h25 : checkRange rowCheck 0 416 = true := by
    simpa only [Nat.reduceAdd] using join_checked h24 range_checked_25
  have h26 : checkRange rowCheck 0 432 = true := by
    simpa only [Nat.reduceAdd] using join_checked h25 range_checked_26
  have h27 : checkRange rowCheck 0 448 = true := by
    simpa only [Nat.reduceAdd] using join_checked h26 range_checked_27
  have h28 : checkRange rowCheck 0 464 = true := by
    simpa only [Nat.reduceAdd] using join_checked h27 range_checked_28
  have h29 : checkRange rowCheck 0 480 = true := by
    simpa only [Nat.reduceAdd] using join_checked h28 range_checked_29
  have h30 : checkRange rowCheck 0 496 = true := by
    simpa only [Nat.reduceAdd] using join_checked h29 range_checked_30
  have h31 : checkRange rowCheck 0 512 = true := by
    simpa only [Nat.reduceAdd] using join_checked h30 range_checked_31
  have h32 : checkRange rowCheck 0 528 = true := by
    simpa only [Nat.reduceAdd] using join_checked h31 range_checked_32
  have h33 : checkRange rowCheck 0 544 = true := by
    simpa only [Nat.reduceAdd] using join_checked h32 range_checked_33
  have h34 : checkRange rowCheck 0 560 = true := by
    simpa only [Nat.reduceAdd] using join_checked h33 range_checked_34
  have h35 : checkRange rowCheck 0 576 = true := by
    simpa only [Nat.reduceAdd] using join_checked h34 range_checked_35
  have h36 : checkRange rowCheck 0 592 = true := by
    simpa only [Nat.reduceAdd] using join_checked h35 range_checked_36
  have h37 : checkRange rowCheck 0 608 = true := by
    simpa only [Nat.reduceAdd] using join_checked h36 range_checked_37
  have h38 : checkRange rowCheck 0 624 = true := by
    simpa only [Nat.reduceAdd] using join_checked h37 range_checked_38
  have h39 : checkRange rowCheck 0 640 = true := by
    simpa only [Nat.reduceAdd] using join_checked h38 range_checked_39
  have h40 : checkRange rowCheck 0 656 = true := by
    simpa only [Nat.reduceAdd] using join_checked h39 range_checked_40
  have h41 : checkRange rowCheck 0 672 = true := by
    simpa only [Nat.reduceAdd] using join_checked h40 range_checked_41
  have h42 : checkRange rowCheck 0 688 = true := by
    simpa only [Nat.reduceAdd] using join_checked h41 range_checked_42
  have h43 : checkRange rowCheck 0 704 = true := by
    simpa only [Nat.reduceAdd] using join_checked h42 range_checked_43
  have h44 : checkRange rowCheck 0 720 = true := by
    simpa only [Nat.reduceAdd] using join_checked h43 range_checked_44
  have h45 : checkRange rowCheck 0 736 = true := by
    simpa only [Nat.reduceAdd] using join_checked h44 range_checked_45
  have h46 : checkRange rowCheck 0 752 = true := by
    simpa only [Nat.reduceAdd] using join_checked h45 range_checked_46
  have h47 : checkRange rowCheck 0 768 = true := by
    simpa only [Nat.reduceAdd] using join_checked h46 range_checked_47
  have h48 : checkRange rowCheck 0 784 = true := by
    simpa only [Nat.reduceAdd] using join_checked h47 range_checked_48
  have h49 : checkRange rowCheck 0 800 = true := by
    simpa only [Nat.reduceAdd] using join_checked h48 range_checked_49
  have h50 : checkRange rowCheck 0 816 = true := by
    simpa only [Nat.reduceAdd] using join_checked h49 range_checked_50
  have h51 : checkRange rowCheck 0 832 = true := by
    simpa only [Nat.reduceAdd] using join_checked h50 range_checked_51
  have h52 : checkRange rowCheck 0 848 = true := by
    simpa only [Nat.reduceAdd] using join_checked h51 range_checked_52
  have h53 : checkRange rowCheck 0 864 = true := by
    simpa only [Nat.reduceAdd] using join_checked h52 range_checked_53
  have h54 : checkRange rowCheck 0 880 = true := by
    simpa only [Nat.reduceAdd] using join_checked h53 range_checked_54
  have h55 : checkRange rowCheck 0 896 = true := by
    simpa only [Nat.reduceAdd] using join_checked h54 range_checked_55
  have h56 : checkRange rowCheck 0 912 = true := by
    simpa only [Nat.reduceAdd] using join_checked h55 range_checked_56
  have h57 : checkRange rowCheck 0 928 = true := by
    simpa only [Nat.reduceAdd] using join_checked h56 range_checked_57
  have h58 : checkRange rowCheck 0 944 = true := by
    simpa only [Nat.reduceAdd] using join_checked h57 range_checked_58
  have h59 : checkRange rowCheck 0 960 = true := by
    simpa only [Nat.reduceAdd] using join_checked h58 range_checked_59
  have h60 : checkRange rowCheck 0 976 = true := by
    simpa only [Nat.reduceAdd] using join_checked h59 range_checked_60
  have h61 : checkRange rowCheck 0 992 = true := by
    simpa only [Nat.reduceAdd] using join_checked h60 range_checked_61
  have h62 : checkRange rowCheck 0 1008 = true := by
    simpa only [Nat.reduceAdd] using join_checked h61 range_checked_62
  have h63 : checkRange rowCheck 0 1024 = true := by
    simpa only [Nat.reduceAdd] using join_checked h62 range_checked_63
  have h64 : checkRange rowCheck 0 1040 = true := by
    simpa only [Nat.reduceAdd] using join_checked h63 range_checked_64
  have h65 : checkRange rowCheck 0 1045 = true := by
    simpa only [Nat.reduceAdd] using join_checked h64 range_checked_65
  exact h65

theorem all_rows_checked (i : Fin 1045) : rowCheck i.val = true :=
  checkRange_sound rowCheck 0 1045 all_ranges_checked i.val (Nat.zero_le _) i.isLt

theorem row_filter_eq (i : Fin 1045) :
    (rowCandidates i.val).filter goodAll = rowExpected i.val := by
  have h := all_rows_checked i
  simpa only [rowCheck,beq_iff_eq] using h

end Paper2.Certificates.DihedralSupport

