import Paper2.Certificates.Q8AtlasSearchCore

/-! Untrusted data for the 236-node, nine-leaf atlas. Every local branch and
incompatibility witness is checked inside Lean, and the generic tree theorem
proves coverage of all compatible normalized decks. -/
namespace Paper2.Certificates.Q8.Atlas

def atlasRows : Fin 9 → Deck :=
  ![![0, 0, 0, 6, 6, 12, 12, 0, 0, 6, 6, 12, 12, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0], ![0, 1, 2, 7, 8, 13, 14, 2, 1, 8, 7, 14, 13, 0, 11, 14, 7, 10, 14, 11, 10, 7, 0, 3, 6, 6, 3, 0], ![0, 2, 1, 8, 7, 14, 13, 1, 2, 7, 8, 13, 14, 0, 14, 11, 10, 7, 11, 14, 7, 10, 0, 6, 3, 3, 6, 0], ![0, 0, 0, 3, 3, 5, 5, 0, 0, 0, 0, 2, 2, 0, 6, 6, 12, 12, 3, 3, 5, 5, 3, 3, 3, 3, 3, 3], ![0, 0, 0, 0, 0, 2, 2, 0, 0, 3, 3, 5, 5, 0, 3, 3, 5, 5, 6, 6, 12, 12, 6, 6, 6, 6, 6, 6], ![0, 6, 6, 6, 6, 9, 9, 3, 3, 6, 6, 6, 6, 3, 3, 6, 7, 7, 3, 6, 7, 7, 0, 14, 14, 11, 11, 11], ![0, 3, 3, 6, 6, 6, 6, 6, 6, 6, 6, 9, 9, 6, 6, 3, 10, 10, 6, 3, 10, 10, 0, 11, 11, 14, 14, 14], ![0, 14, 14, 12, 12, 12, 12, 11, 11, 9, 9, 12, 12, 11, 11, 11, 5, 12, 11, 11, 5, 12, 11, 11, 14, 11, 14, 0], ![0, 11, 11, 9, 9, 12, 12, 14, 14, 12, 12, 12, 12, 14, 14, 14, 12, 5, 14, 14, 12, 5, 14, 14, 11, 14, 11, 0]]

private def node0 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none],none,13,![some 1, none, none, some 128, none, none, some 155, none, none, none, none, some 182, none, none, some 209],![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

private def node1 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, none, none, none, none, none, none, none, none, some 0, none, none, none, none, none, none, none, none, none, none, none, none, none, none],none,22,![some 2, none, none, some 76, none, none, some 102, none, none, none, none, none, none, none, none],![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 13]⟩

private def node2 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, none, none, none, none, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, none],none,27,![some 3, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 22, 0, 0, 22, 0, 0, 0, 0, 13, 0, 0, 13]⟩

private def node3 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, none, none, none, none, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,1,![some 4, some 28, some 52, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 27, 22, 22, 27, 22, 22, 22, 22, 22, 22, 22, 22]⟩

private def node4 : SearchNode 236 9 :=
  ⟨![some 0, some 0, none, none, none, none, none, none, none, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,8,![some 5, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 1, 1, 27, 1, 1, 27, 1, 1, 1, 1, 22, 1, 1, 22]⟩

private def node5 : SearchNode 236 9 :=
  ⟨![some 0, some 0, none, none, none, none, none, none, some 0, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,3,![none, none, none, none, none, none, some 6, none, none, none, none, none, none, none, none],![27, 8, 8, 27, 8, 8, 0, 8, 8, 8, 13, 8, 8, 13, 8]⟩

private def node6 : SearchNode 236 9 :=
  ⟨![some 0, some 0, none, some 6, none, none, none, none, some 0, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,4,![none, none, none, none, none, none, some 7, none, none, none, none, none, none, none, none],![27, 8, 8, 27, 8, 8, 0, 8, 8, 8, 13, 8, 8, 13, 8]⟩

private def node7 : SearchNode 236 9 :=
  ⟨![some 0, some 0, none, some 6, some 6, none, none, none, some 0, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,5,![none, none, none, none, none, none, none, none, none, none, none, none, some 8, none, none],![8, 8, 22, 8, 8, 22, 8, 8, 13, 8, 8, 13, 0, 8, 8]⟩

private def node8 : SearchNode 236 9 :=
  ⟨![some 0, some 0, none, some 6, some 6, some 12, none, none, some 0, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,6,![none, none, none, none, none, none, none, none, none, none, none, none, some 9, none, none],![8, 8, 22, 8, 8, 22, 8, 8, 13, 8, 8, 13, 0, 8, 8]⟩

private def node9 : SearchNode 236 9 :=
  ⟨![some 0, some 0, none, some 6, some 6, some 12, some 12, none, some 0, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,7,![some 10, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 3, 3, 5, 3, 3, 5, 3, 3, 3, 4, 3, 3, 4, 3]⟩

private def node10 : SearchNode 236 9 :=
  ⟨![some 0, some 0, none, some 6, some 6, some 12, some 12, some 0, some 0, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,2,![some 11, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 7, 7, 27, 7, 7, 27, 7, 7, 7, 7, 22, 7, 7, 22]⟩

private def node11 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,9,![none, none, none, none, none, none, some 12, none, none, none, none, none, none, none, none],![5, 1, 1, 5, 1, 1, 0, 1, 1, 1, 1, 2, 1, 1, 2]⟩

private def node12 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 6, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,10,![none, none, none, none, none, none, some 13, none, none, none, none, none, none, none, none],![5, 1, 1, 5, 1, 1, 0, 1, 1, 1, 1, 2, 1, 1, 2]⟩

private def node13 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 6, some 6, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,11,![none, none, none, none, none, none, none, none, none, none, none, none, some 14, none, none],![1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 1, 0, 1, 1]⟩

private def node14 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 6, some 6, some 12, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,12,![none, none, none, none, none, none, none, none, none, none, none, none, some 15, none, none],![1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 1, 0, 1, 1]⟩

private def node15 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 6, some 6, some 12, some 12, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,14,![some 16, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 5, 0, 0, 5, 0, 0, 0, 0, 2, 0, 0, 2]⟩

private def node16 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,15,![some 17, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 5, 0, 0, 5, 0, 0, 0, 0, 2, 0, 0, 2]⟩

private def node17 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 0, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,16,![none, none, some 18, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 0, 0, 3, 0, 2, 0, 0, 2, 0, 3, 0, 0]⟩

private def node18 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 0, some 2, none, none, none, none, none, some 0, none, none, none, none, some 0],none,17,![none, none, some 19, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 0, 0, 3, 0, 2, 0, 0, 2, 0, 3, 0, 0]⟩

private def node19 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 0, some 2, some 2, none, none, none, none, some 0, none, none, none, none, some 0],none,18,![some 20, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 5, 0, 0, 5, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node20 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 0, some 2, some 2, some 0, none, none, none, some 0, none, none, none, none, some 0],none,19,![some 21, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 5, 0, 0, 5, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node21 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 0, some 2, some 2, some 0, some 0, none, none, some 0, none, none, none, none, some 0],none,20,![none, none, some 22, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 1, 0, 3, 0, 0]⟩

private def node22 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 2, none, some 0, none, none, none, none, some 0],none,21,![none, none, some 23, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 1, 0, 3, 0, 0]⟩

private def node23 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 2, some 2, some 0, none, none, none, none, some 0],none,23,![some 24, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 4, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node24 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 2, some 2, some 0, some 0, none, none, none, some 0],none,24,![some 25, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 4, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node25 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 2, some 2, some 0, some 0, some 0, none, none, some 0],none,25,![some 26, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node26 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 2, some 2, some 0, some 0, some 0, some 0, none, some 0],none,26,![some 27, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node27 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 6, some 6, some 12, some 12, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 2, some 2, some 0, some 0, some 0, some 0, some 0, some 0],some 0,0,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

private def node28 : SearchNode 236 9 :=
  ⟨![some 0, some 1, none, none, none, none, none, none, none, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,8,![none, some 29, none, none, none, none, none, none, none, none, none, none, none, none, none],![1, 0, 1, 1, 22, 1, 1, 1, 22, 22, 1, 1, 1, 22, 1]⟩

private def node29 : SearchNode 236 9 :=
  ⟨![some 0, some 1, none, none, none, none, none, none, some 1, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,3,![none, none, none, none, none, none, none, some 30, none, none, none, none, none, none, none],![8, 13, 8, 8, 13, 8, 8, 0, 8, 13, 8, 8, 8, 8, 13]⟩

private def node30 : SearchNode 236 9 :=
  ⟨![some 0, some 1, none, some 7, none, none, none, none, some 1, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,4,![none, none, none, none, none, none, none, none, some 31, none, none, none, none, none, none],![8, 8, 13, 8, 8, 13, 8, 8, 0, 8, 8, 13, 13, 8, 8]⟩

private def node31 : SearchNode 236 9 :=
  ⟨![some 0, some 1, none, some 7, some 8, none, none, none, some 1, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,5,![none, none, none, none, none, none, none, none, none, none, none, none, none, some 32, none],![13, 8, 8, 13, 8, 8, 13, 8, 8, 8, 13, 8, 8, 0, 8]⟩

private def node32 : SearchNode 236 9 :=
  ⟨![some 0, some 1, none, some 7, some 8, some 13, none, none, some 1, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,6,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 33],![8, 13, 8, 8, 13, 8, 8, 13, 8, 13, 8, 8, 8, 8, 0]⟩

private def node33 : SearchNode 236 9 :=
  ⟨![some 0, some 1, none, some 7, some 8, some 13, some 14, none, some 1, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,7,![none, none, some 34, none, none, none, none, none, none, none, none, none, none, none, none],![3, 3, 0, 3, 3, 4, 3, 3, 4, 3, 3, 4, 4, 3, 3]⟩

private def node34 : SearchNode 236 9 :=
  ⟨![some 0, some 1, none, some 7, some 8, some 13, some 14, some 2, some 1, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,2,![none, none, some 35, none, none, none, none, none, none, none, none, none, none, none, none],![7, 7, 0, 7, 7, 22, 7, 22, 7, 7, 22, 7, 22, 7, 7]⟩

private def node35 : SearchNode 236 9 :=
  ⟨![some 0, some 1, some 2, some 7, some 8, some 13, some 14, some 2, some 1, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,9,![none, none, none, none, none, none, none, none, some 36, none, none, none, none, none, none],![1, 2, 1, 1, 2, 1, 1, 1, 0, 2, 1, 1, 1, 2, 1]⟩

private def node36 : SearchNode 236 9 :=
  ⟨![some 0, some 1, some 2, some 7, some 8, some 13, some 14, some 2, some 1, some 8, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,10,![none, none, none, none, none, none, none, some 37, none, none, none, none, none, none, none],![1, 1, 2, 1, 1, 2, 1, 0, 1, 1, 2, 1, 2, 1, 1]⟩

private def node37 : SearchNode 236 9 :=
  ⟨![some 0, some 1, some 2, some 7, some 8, some 13, some 14, some 2, some 1, some 8, some 7, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,11,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 38],![2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 0]⟩

private def node38 : SearchNode 236 9 :=
  ⟨![some 0, some 1, some 2, some 7, some 8, some 13, some 14, some 2, some 1, some 8, some 7, some 14, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,12,![none, none, none, none, none, none, none, none, none, none, none, none, none, some 39, none],![1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 0, 1]⟩

private def node39 : SearchNode 236 9 :=
  ⟨![some 0, some 1, some 2, some 7, some 8, some 13, some 14, some 2, some 1, some 8, some 7, some 14, some 13, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,14,![none, none, none, none, none, none, none, none, none, none, none, some 40, none, none, none],![2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2]⟩

private def node40 : SearchNode 236 9 :=
  ⟨![some 0, some 1, some 2, some 7, some 8, some 13, some 14, some 2, some 1, some 8, some 7, some 14, some 13, some 0, some 11, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,15,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 41],![2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0]⟩

private def node41 : SearchNode 236 9 :=
  ⟨![some 0, some 1, some 2, some 7, some 8, some 13, some 14, some 2, some 1, some 8, some 7, some 14, some 13, some 0, some 11, some 14, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,16,![none, none, none, none, none, none, none, some 42, none, none, none, none, none, none, none],![0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0]⟩

private def node42 : SearchNode 236 9 :=
  ⟨![some 0, some 1, some 2, some 7, some 8, some 13, some 14, some 2, some 1, some 8, some 7, some 14, some 13, some 0, some 11, some 14, some 7, none, none, none, none, none, some 0, none, none, none, none, some 0],none,17,![none, none, none, none, none, none, none, none, none, none, some 43, none, none, none, none],![0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0]⟩

private def node43 : SearchNode 236 9 :=
  ⟨![some 0, some 1, some 2, some 7, some 8, some 13, some 14, some 2, some 1, some 8, some 7, some 14, some 13, some 0, some 11, some 14, some 7, some 10, none, none, none, none, some 0, none, none, none, none, some 0],none,18,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 44],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]⟩

private def node44 : SearchNode 236 9 :=
  ⟨![some 0, some 1, some 2, some 7, some 8, some 13, some 14, some 2, some 1, some 8, some 7, some 14, some 13, some 0, some 11, some 14, some 7, some 10, some 14, none, none, none, some 0, none, none, none, none, some 0],none,19,![none, none, none, none, none, none, none, none, none, none, none, some 45, none, none, none],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]⟩

private def node45 : SearchNode 236 9 :=
  ⟨![some 0, some 1, some 2, some 7, some 8, some 13, some 14, some 2, some 1, some 8, some 7, some 14, some 13, some 0, some 11, some 14, some 7, some 10, some 14, some 11, none, none, some 0, none, none, none, none, some 0],none,20,![none, none, none, none, none, none, none, none, none, none, some 46, none, none, none, none],![0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0]⟩

private def node46 : SearchNode 236 9 :=
  ⟨![some 0, some 1, some 2, some 7, some 8, some 13, some 14, some 2, some 1, some 8, some 7, some 14, some 13, some 0, some 11, some 14, some 7, some 10, some 14, some 11, some 10, none, some 0, none, none, none, none, some 0],none,21,![none, none, none, none, none, none, none, some 47, none, none, none, none, none, none, none],![0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0]⟩

private def node47 : SearchNode 236 9 :=
  ⟨![some 0, some 1, some 2, some 7, some 8, some 13, some 14, some 2, some 1, some 8, some 7, some 14, some 13, some 0, some 11, some 14, some 7, some 10, some 14, some 11, some 10, some 7, some 0, none, none, none, none, some 0],none,23,![none, none, none, some 48, none, none, none, none, none, none, none, none, none, none, none],![4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node48 : SearchNode 236 9 :=
  ⟨![some 0, some 1, some 2, some 7, some 8, some 13, some 14, some 2, some 1, some 8, some 7, some 14, some 13, some 0, some 11, some 14, some 7, some 10, some 14, some 11, some 10, some 7, some 0, some 3, none, none, none, some 0],none,24,![none, none, none, none, none, none, some 49, none, none, none, none, none, none, none, none],![4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node49 : SearchNode 236 9 :=
  ⟨![some 0, some 1, some 2, some 7, some 8, some 13, some 14, some 2, some 1, some 8, some 7, some 14, some 13, some 0, some 11, some 14, some 7, some 10, some 14, some 11, some 10, some 7, some 0, some 3, some 6, none, none, some 0],none,25,![none, none, none, none, none, none, some 50, none, none, none, none, none, none, none, none],![3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node50 : SearchNode 236 9 :=
  ⟨![some 0, some 1, some 2, some 7, some 8, some 13, some 14, some 2, some 1, some 8, some 7, some 14, some 13, some 0, some 11, some 14, some 7, some 10, some 14, some 11, some 10, some 7, some 0, some 3, some 6, some 6, none, some 0],none,26,![none, none, none, some 51, none, none, none, none, none, none, none, none, none, none, none],![3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node51 : SearchNode 236 9 :=
  ⟨![some 0, some 1, some 2, some 7, some 8, some 13, some 14, some 2, some 1, some 8, some 7, some 14, some 13, some 0, some 11, some 14, some 7, some 10, some 14, some 11, some 10, some 7, some 0, some 3, some 6, some 6, some 3, some 0],some 1,0,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

private def node52 : SearchNode 236 9 :=
  ⟨![some 0, some 2, none, none, none, none, none, none, none, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,8,![none, none, some 53, none, none, none, none, none, none, none, none, none, none, none, none],![1, 1, 0, 1, 1, 22, 1, 22, 1, 1, 22, 1, 22, 1, 1]⟩

private def node53 : SearchNode 236 9 :=
  ⟨![some 0, some 2, none, none, none, none, none, none, some 2, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,3,![none, none, none, none, none, none, none, none, some 54, none, none, none, none, none, none],![8, 8, 13, 8, 8, 13, 8, 8, 0, 8, 8, 13, 13, 8, 8]⟩

private def node54 : SearchNode 236 9 :=
  ⟨![some 0, some 2, none, some 8, none, none, none, none, some 2, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,4,![none, none, none, none, none, none, none, some 55, none, none, none, none, none, none, none],![8, 13, 8, 8, 13, 8, 8, 0, 8, 13, 8, 8, 8, 8, 13]⟩

private def node55 : SearchNode 236 9 :=
  ⟨![some 0, some 2, none, some 8, some 7, none, none, none, some 2, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,5,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 56],![8, 13, 8, 8, 13, 8, 8, 13, 8, 13, 8, 8, 8, 8, 0]⟩

private def node56 : SearchNode 236 9 :=
  ⟨![some 0, some 2, none, some 8, some 7, some 14, none, none, some 2, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,6,![none, none, none, none, none, none, none, none, none, none, none, none, none, some 57, none],![13, 8, 8, 13, 8, 8, 13, 8, 8, 8, 13, 8, 8, 0, 8]⟩

private def node57 : SearchNode 236 9 :=
  ⟨![some 0, some 2, none, some 8, some 7, some 14, some 13, none, some 2, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,7,![none, some 58, none, none, none, none, none, none, none, none, none, none, none, none, none],![3, 0, 3, 3, 4, 3, 3, 4, 3, 4, 3, 3, 3, 3, 4]⟩

private def node58 : SearchNode 236 9 :=
  ⟨![some 0, some 2, none, some 8, some 7, some 14, some 13, some 1, some 2, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,2,![none, some 59, none, none, none, none, none, none, none, none, none, none, none, none, none],![7, 0, 7, 7, 22, 7, 7, 7, 22, 22, 7, 7, 7, 22, 7]⟩

private def node59 : SearchNode 236 9 :=
  ⟨![some 0, some 2, some 1, some 8, some 7, some 14, some 13, some 1, some 2, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,9,![none, none, none, none, none, none, none, some 60, none, none, none, none, none, none, none],![1, 1, 2, 1, 1, 2, 1, 0, 1, 1, 2, 1, 2, 1, 1]⟩

private def node60 : SearchNode 236 9 :=
  ⟨![some 0, some 2, some 1, some 8, some 7, some 14, some 13, some 1, some 2, some 7, none, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,10,![none, none, none, none, none, none, none, none, some 61, none, none, none, none, none, none],![1, 2, 1, 1, 2, 1, 1, 1, 0, 2, 1, 1, 1, 2, 1]⟩

private def node61 : SearchNode 236 9 :=
  ⟨![some 0, some 2, some 1, some 8, some 7, some 14, some 13, some 1, some 2, some 7, some 8, none, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,11,![none, none, none, none, none, none, none, none, none, none, none, none, none, some 62, none],![1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 0, 1]⟩

private def node62 : SearchNode 236 9 :=
  ⟨![some 0, some 2, some 1, some 8, some 7, some 14, some 13, some 1, some 2, some 7, some 8, some 13, none, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,12,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 63],![2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 0]⟩

private def node63 : SearchNode 236 9 :=
  ⟨![some 0, some 2, some 1, some 8, some 7, some 14, some 13, some 1, some 2, some 7, some 8, some 13, some 14, some 0, none, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,14,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 64],![2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0]⟩

private def node64 : SearchNode 236 9 :=
  ⟨![some 0, some 2, some 1, some 8, some 7, some 14, some 13, some 1, some 2, some 7, some 8, some 13, some 14, some 0, some 14, none, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,15,![none, none, none, none, none, none, none, none, none, none, none, some 65, none, none, none],![2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2]⟩

private def node65 : SearchNode 236 9 :=
  ⟨![some 0, some 2, some 1, some 8, some 7, some 14, some 13, some 1, some 2, some 7, some 8, some 13, some 14, some 0, some 14, some 11, none, none, none, none, none, none, some 0, none, none, none, none, some 0],none,16,![none, none, none, none, none, none, none, none, none, none, some 66, none, none, none, none],![0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0]⟩

private def node66 : SearchNode 236 9 :=
  ⟨![some 0, some 2, some 1, some 8, some 7, some 14, some 13, some 1, some 2, some 7, some 8, some 13, some 14, some 0, some 14, some 11, some 10, none, none, none, none, none, some 0, none, none, none, none, some 0],none,17,![none, none, none, none, none, none, none, some 67, none, none, none, none, none, none, none],![0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0]⟩

private def node67 : SearchNode 236 9 :=
  ⟨![some 0, some 2, some 1, some 8, some 7, some 14, some 13, some 1, some 2, some 7, some 8, some 13, some 14, some 0, some 14, some 11, some 10, some 7, none, none, none, none, some 0, none, none, none, none, some 0],none,18,![none, none, none, none, none, none, none, none, none, none, none, some 68, none, none, none],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]⟩

private def node68 : SearchNode 236 9 :=
  ⟨![some 0, some 2, some 1, some 8, some 7, some 14, some 13, some 1, some 2, some 7, some 8, some 13, some 14, some 0, some 14, some 11, some 10, some 7, some 11, none, none, none, some 0, none, none, none, none, some 0],none,19,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 69],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]⟩

private def node69 : SearchNode 236 9 :=
  ⟨![some 0, some 2, some 1, some 8, some 7, some 14, some 13, some 1, some 2, some 7, some 8, some 13, some 14, some 0, some 14, some 11, some 10, some 7, some 11, some 14, none, none, some 0, none, none, none, none, some 0],none,20,![none, none, none, none, none, none, none, some 70, none, none, none, none, none, none, none],![0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0]⟩

private def node70 : SearchNode 236 9 :=
  ⟨![some 0, some 2, some 1, some 8, some 7, some 14, some 13, some 1, some 2, some 7, some 8, some 13, some 14, some 0, some 14, some 11, some 10, some 7, some 11, some 14, some 7, none, some 0, none, none, none, none, some 0],none,21,![none, none, none, none, none, none, none, none, none, none, some 71, none, none, none, none],![0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0]⟩

private def node71 : SearchNode 236 9 :=
  ⟨![some 0, some 2, some 1, some 8, some 7, some 14, some 13, some 1, some 2, some 7, some 8, some 13, some 14, some 0, some 14, some 11, some 10, some 7, some 11, some 14, some 7, some 10, some 0, none, none, none, none, some 0],none,23,![none, none, none, none, none, none, some 72, none, none, none, none, none, none, none, none],![4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node72 : SearchNode 236 9 :=
  ⟨![some 0, some 2, some 1, some 8, some 7, some 14, some 13, some 1, some 2, some 7, some 8, some 13, some 14, some 0, some 14, some 11, some 10, some 7, some 11, some 14, some 7, some 10, some 0, some 6, none, none, none, some 0],none,24,![none, none, none, some 73, none, none, none, none, none, none, none, none, none, none, none],![4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node73 : SearchNode 236 9 :=
  ⟨![some 0, some 2, some 1, some 8, some 7, some 14, some 13, some 1, some 2, some 7, some 8, some 13, some 14, some 0, some 14, some 11, some 10, some 7, some 11, some 14, some 7, some 10, some 0, some 6, some 3, none, none, some 0],none,25,![none, none, none, some 74, none, none, none, none, none, none, none, none, none, none, none],![3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node74 : SearchNode 236 9 :=
  ⟨![some 0, some 2, some 1, some 8, some 7, some 14, some 13, some 1, some 2, some 7, some 8, some 13, some 14, some 0, some 14, some 11, some 10, some 7, some 11, some 14, some 7, some 10, some 0, some 6, some 3, some 3, none, some 0],none,26,![none, none, none, none, none, none, some 75, none, none, none, none, none, none, none, none],![3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node75 : SearchNode 236 9 :=
  ⟨![some 0, some 2, some 1, some 8, some 7, some 14, some 13, some 1, some 2, some 7, some 8, some 13, some 14, some 0, some 14, some 11, some 10, some 7, some 11, some 14, some 7, some 10, some 0, some 6, some 3, some 3, some 6, some 0],some 2,0,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

private def node76 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, none, none, none, none, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 3, none, none, none, none, none],none,5,![none, none, none, none, none, some 77, none, none, none, none, none, none, none, none, none],![13, 13, 22, 13, 13, 0, 13, 13, 13, 13, 13, 13, 22, 22, 22]⟩

private def node77 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, some 5, none, none, none, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 3, none, none, none, none, none],none,6,![none, none, none, none, none, some 78, none, none, none, none, none, none, none, none, none],![13, 13, 22, 13, 13, 0, 13, 13, 13, 13, 13, 13, 22, 22, 22]⟩

private def node78 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, some 5, some 5, none, none, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 3, none, none, none, none, none],none,7,![some 79, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 5, 5, 5, 5, 6, 5, 5, 6, 5, 5, 22, 5, 5, 22]⟩

private def node79 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, some 5, some 5, some 0, none, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 3, none, none, none, none, none],none,8,![some 80, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 5, 5, 5, 5, 6, 5, 5, 6, 5, 5, 22, 5, 5, 22]⟩

private def node80 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, some 5, some 5, some 0, some 0, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 3, none, none, none, none, none],none,9,![some 81, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 5, 5, 5, 5, 6, 5, 5, 6, 5, 5, 13, 5, 5, 13]⟩

private def node81 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, some 5, some 5, some 0, some 0, some 0, none, none, none, some 0, none, none, none, none, none, none, none, none, some 3, none, none, none, none, none],none,10,![some 82, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 5, 5, 5, 5, 6, 5, 5, 6, 5, 5, 13, 5, 5, 13]⟩

private def node82 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, some 5, some 5, some 0, some 0, some 0, some 0, none, none, some 0, none, none, none, none, none, none, none, none, some 3, none, none, none, none, none],none,11,![none, none, some 83, none, none, none, none, none, none, none, none, none, none, none, none],![6, 6, 0, 6, 6, 22, 13, 6, 6, 13, 6, 6, 22, 6, 6]⟩

private def node83 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, some 5, some 5, some 0, some 0, some 0, some 0, some 2, none, some 0, none, none, none, none, none, none, none, none, some 3, none, none, none, none, none],none,1,![some 84, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 8, 8, 11, 8, 8, 11, 8, 8, 8, 8, 9, 8, 8, 9]⟩

private def node84 : SearchNode 236 9 :=
  ⟨![some 0, some 0, none, none, none, some 5, some 5, some 0, some 0, some 0, some 0, some 2, none, some 0, none, none, none, none, none, none, none, none, some 3, none, none, none, none, none],none,2,![some 85, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 7, 7, 11, 7, 7, 11, 7, 7, 7, 7, 9, 7, 7, 9]⟩

private def node85 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, none, none, some 5, some 5, some 0, some 0, some 0, some 0, some 2, none, some 0, none, none, none, none, none, none, none, none, some 3, none, none, none, none, none],none,3,![none, none, none, some 86, none, none, none, none, none, none, none, none, none, none, none],![11, 7, 7, 0, 7, 7, 11, 7, 7, 7, 7, 8, 7, 7, 8]⟩

private def node86 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 3, none, some 5, some 5, some 0, some 0, some 0, some 0, some 2, none, some 0, none, none, none, none, none, none, none, none, some 3, none, none, none, none, none],none,4,![none, none, none, some 87, none, none, none, none, none, none, none, none, none, none, none],![11, 7, 7, 0, 7, 7, 11, 7, 7, 7, 7, 8, 7, 7, 8]⟩

private def node87 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 0, some 0, some 0, some 2, none, some 0, none, none, none, none, none, none, none, none, some 3, none, none, none, none, none],none,12,![none, none, some 88, none, none, none, none, none, none, none, none, none, none, none, none],![1, 1, 0, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 1]⟩

private def node88 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 0, some 0, some 0, some 2, some 2, some 0, none, none, none, none, none, none, none, none, some 3, none, none, none, none, none],none,14,![none, none, none, none, none, none, some 89, none, none, none, none, none, none, none, none],![5, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2]⟩

private def node89 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 6, none, none, none, none, none, none, none, some 3, none, none, none, none, none],none,15,![none, none, none, none, none, none, some 90, none, none, none, none, none, none, none, none],![5, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2]⟩

private def node90 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 6, some 6, none, none, none, none, none, none, some 3, none, none, none, none, none],none,16,![none, none, none, none, none, none, none, none, none, none, none, none, some 91, none, none],![0, 0, 3, 0, 0, 3, 0, 2, 0, 0, 2, 0, 0, 0, 0]⟩

private def node91 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 6, some 6, some 12, none, none, none, none, none, some 3, none, none, none, none, none],none,17,![none, none, none, none, none, none, none, none, none, none, none, none, some 92, none, none],![0, 0, 3, 0, 0, 3, 0, 2, 0, 0, 2, 0, 0, 0, 0]⟩

private def node92 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 6, some 6, some 12, some 12, none, none, none, none, some 3, none, none, none, none, none],none,18,![none, none, none, some 93, none, none, none, none, none, none, none, none, none, none, none],![5, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node93 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 6, some 6, some 12, some 12, some 3, none, none, none, some 3, none, none, none, none, none],none,19,![none, none, none, some 94, none, none, none, none, none, none, none, none, none, none, none],![5, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node94 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 6, some 6, some 12, some 12, some 3, some 3, none, none, some 3, none, none, none, none, none],none,20,![none, none, none, none, none, some 95, none, none, none, none, none, none, none, none, none],![0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 1, 0, 3, 0, 0]⟩

private def node95 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 6, some 6, some 12, some 12, some 3, some 3, some 5, none, some 3, none, none, none, none, none],none,21,![none, none, none, none, none, some 96, none, none, none, none, none, none, none, none, none],![0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 1, 0, 3, 0, 0]⟩

private def node96 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 6, some 6, some 12, some 12, some 3, some 3, some 5, some 5, some 3, none, none, none, none, none],none,23,![none, none, none, some 97, none, none, none, none, none, none, none, none, none, none, none],![4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node97 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 6, some 6, some 12, some 12, some 3, some 3, some 5, some 5, some 3, some 3, none, none, none, none],none,24,![none, none, none, some 98, none, none, none, none, none, none, none, none, none, none, none],![4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node98 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 6, some 6, some 12, some 12, some 3, some 3, some 5, some 5, some 3, some 3, some 3, none, none, none],none,25,![none, none, none, some 99, none, none, none, none, none, none, none, none, none, none, none],![3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node99 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 6, some 6, some 12, some 12, some 3, some 3, some 5, some 5, some 3, some 3, some 3, some 3, none, none],none,26,![none, none, none, some 100, none, none, none, none, none, none, none, none, none, none, none],![3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node100 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 6, some 6, some 12, some 12, some 3, some 3, some 5, some 5, some 3, some 3, some 3, some 3, some 3, none],none,27,![none, none, none, some 101, none, none, none, none, none, none, none, none, none, none, none],![3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node101 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 6, some 6, some 12, some 12, some 3, some 3, some 5, some 5, some 3, some 3, some 3, some 3, some 3, some 3],some 3,0,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

private def node102 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, none, none, none, none, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 6, none, none, none, none, none],none,5,![none, none, some 103, none, none, none, none, none, none, none, none, none, none, none, none],![13, 13, 0, 13, 13, 22, 13, 13, 13, 13, 13, 13, 22, 22, 22]⟩

private def node103 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, some 2, none, none, none, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 6, none, none, none, none, none],none,6,![none, none, some 104, none, none, none, none, none, none, none, none, none, none, none, none],![13, 13, 0, 13, 13, 22, 13, 13, 13, 13, 13, 13, 22, 22, 22]⟩

private def node104 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, some 2, some 2, none, none, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 6, none, none, none, none, none],none,7,![some 105, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 5, 5, 5, 5, 6, 5, 5, 6, 5, 5, 22, 5, 5, 22]⟩

private def node105 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, some 2, some 2, some 0, none, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 6, none, none, none, none, none],none,8,![some 106, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 5, 5, 5, 5, 6, 5, 5, 6, 5, 5, 22, 5, 5, 22]⟩

private def node106 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, some 2, some 2, some 0, some 0, none, none, none, none, some 0, none, none, none, none, none, none, none, none, some 6, none, none, none, none, none],none,9,![none, none, none, some 107, none, none, none, none, none, none, none, none, none, none, none],![5, 5, 6, 0, 5, 5, 5, 6, 5, 5, 13, 5, 5, 13, 5]⟩

private def node107 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, some 2, some 2, some 0, some 0, some 3, none, none, none, some 0, none, none, none, none, none, none, none, none, some 6, none, none, none, none, none],none,10,![none, none, none, some 108, none, none, none, none, none, none, none, none, none, none, none],![5, 5, 6, 0, 5, 5, 5, 6, 5, 5, 13, 5, 5, 13, 5]⟩

private def node108 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, some 2, some 2, some 0, some 0, some 3, some 3, none, none, some 0, none, none, none, none, none, none, none, none, some 6, none, none, none, none, none],none,11,![none, none, none, none, none, some 109, none, none, none, none, none, none, none, none, none],![6, 6, 22, 6, 6, 0, 13, 6, 6, 13, 6, 6, 22, 6, 6]⟩

private def node109 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, some 2, some 2, some 0, some 0, some 3, some 3, some 5, none, some 0, none, none, none, none, none, none, none, none, some 6, none, none, none, none, none],none,1,![some 110, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 8, 8, 11, 8, 8, 11, 8, 8, 8, 8, 9, 8, 8, 9]⟩

private def node110 : SearchNode 236 9 :=
  ⟨![some 0, some 0, none, none, none, some 2, some 2, some 0, some 0, some 3, some 3, some 5, none, some 0, none, none, none, none, none, none, none, none, some 6, none, none, none, none, none],none,2,![some 111, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 7, 7, 11, 7, 7, 11, 7, 7, 7, 7, 9, 7, 7, 9]⟩

private def node111 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, none, none, some 2, some 2, some 0, some 0, some 3, some 3, some 5, none, some 0, none, none, none, none, none, none, none, none, some 6, none, none, none, none, none],none,3,![some 112, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 7, 7, 11, 7, 7, 11, 7, 7, 7, 7, 8, 7, 7, 8]⟩

private def node112 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 0, none, some 2, some 2, some 0, some 0, some 3, some 3, some 5, none, some 0, none, none, none, none, none, none, none, none, some 6, none, none, none, none, none],none,4,![some 113, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 7, 7, 11, 7, 7, 11, 7, 7, 7, 7, 8, 7, 7, 8]⟩

private def node113 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 3, some 3, some 5, none, some 0, none, none, none, none, none, none, none, none, some 6, none, none, none, none, none],none,12,![none, none, none, none, none, some 114, none, none, none, none, none, none, none, none, none],![1, 1, 3, 1, 1, 0, 1, 2, 1, 1, 2, 1, 3, 1, 1]⟩

private def node114 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 3, some 3, some 5, some 5, some 0, none, none, none, none, none, none, none, none, some 6, none, none, none, none, none],none,14,![none, none, none, some 115, none, none, none, none, none, none, none, none, none, none, none],![5, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 2, 0, 0, 2]⟩

private def node115 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 3, none, none, none, none, none, none, none, some 6, none, none, none, none, none],none,15,![none, none, none, some 116, none, none, none, none, none, none, none, none, none, none, none],![5, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 2, 0, 0, 2]⟩

private def node116 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 3, some 3, none, none, none, none, none, none, some 6, none, none, none, none, none],none,16,![none, none, none, none, none, some 117, none, none, none, none, none, none, none, none, none],![0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 2, 0, 3, 0, 0]⟩

private def node117 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 3, some 3, some 5, none, none, none, none, none, some 6, none, none, none, none, none],none,17,![none, none, none, none, none, some 118, none, none, none, none, none, none, none, none, none],![0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 2, 0, 3, 0, 0]⟩

private def node118 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 3, some 3, some 5, some 5, none, none, none, none, some 6, none, none, none, none, none],none,18,![none, none, none, none, none, none, some 119, none, none, none, none, none, none, none, none],![5, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node119 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 3, some 3, some 5, some 5, some 6, none, none, none, some 6, none, none, none, none, none],none,19,![none, none, none, none, none, none, some 120, none, none, none, none, none, none, none, none],![5, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node120 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 3, some 3, some 5, some 5, some 6, some 6, none, none, some 6, none, none, none, none, none],none,20,![none, none, none, none, none, none, none, none, none, none, none, none, some 121, none, none],![0, 0, 3, 0, 0, 3, 0, 1, 0, 0, 1, 0, 0, 0, 0]⟩

private def node121 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 3, some 3, some 5, some 5, some 6, some 6, some 12, none, some 6, none, none, none, none, none],none,21,![none, none, none, none, none, none, none, none, none, none, none, none, some 122, none, none],![0, 0, 3, 0, 0, 3, 0, 1, 0, 0, 1, 0, 0, 0, 0]⟩

private def node122 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 3, some 3, some 5, some 5, some 6, some 6, some 12, some 12, some 6, none, none, none, none, none],none,23,![none, none, none, none, none, none, some 123, none, none, none, none, none, none, none, none],![4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node123 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 3, some 3, some 5, some 5, some 6, some 6, some 12, some 12, some 6, some 6, none, none, none, none],none,24,![none, none, none, none, none, none, some 124, none, none, none, none, none, none, none, none],![4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node124 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 3, some 3, some 5, some 5, some 6, some 6, some 12, some 12, some 6, some 6, some 6, none, none, none],none,25,![none, none, none, none, none, none, some 125, none, none, none, none, none, none, none, none],![3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node125 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 3, some 3, some 5, some 5, some 6, some 6, some 12, some 12, some 6, some 6, some 6, some 6, none, none],none,26,![none, none, none, none, none, none, some 126, none, none, none, none, none, none, none, none],![3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node126 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 3, some 3, some 5, some 5, some 6, some 6, some 12, some 12, some 6, some 6, some 6, some 6, some 6, none],none,27,![none, none, none, none, none, none, some 127, none, none, none, none, none, none, none, none],![3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node127 : SearchNode 236 9 :=
  ⟨![some 0, some 0, some 0, some 0, some 0, some 2, some 2, some 0, some 0, some 3, some 3, some 5, some 5, some 0, some 3, some 3, some 5, some 5, some 6, some 6, some 12, some 12, some 6, some 6, some 6, some 6, some 6, some 6],some 4,0,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

private def node128 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, none, none, none, none, none, none, none, none, some 3, none, none, none, none, none, none, none, none, none, none, none, none, none, none],none,23,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 129],![13, 0, 0, 13, 0, 0, 13, 0, 0, 0, 0, 13, 0, 0, 0]⟩

private def node129 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, none, none, none, none, none, none, none, none, some 3, none, none, none, none, none, none, none, none, none, some 14, none, none, none, none],none,4,![none, none, none, none, none, none, some 130, none, none, none, none, none, none, none, none],![23, 13, 13, 23, 13, 13, 0, 23, 23, 13, 13, 13, 13, 13, 13]⟩

private def node130 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, some 6, none, none, none, none, none, none, none, none, some 3, none, none, none, none, none, none, none, none, none, some 14, none, none, none, none],none,10,![none, none, none, none, none, none, some 131, none, none, none, none, none, none, none, none],![23, 13, 13, 23, 13, 13, 0, 23, 23, 13, 13, 13, 13, 13, 13]⟩

private def node131 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, some 6, none, none, none, none, none, some 6, none, none, some 3, none, none, none, none, none, none, none, none, none, some 14, none, none, none, none],none,1,![none, none, none, none, none, none, some 132, none, none, none, none, none, none, none, none],![23, 10, 10, 23, 10, 10, 0, 10, 10, 23, 10, 10, 23, 10, 10]⟩

private def node132 : SearchNode 236 9 :=
  ⟨![some 0, some 6, none, none, some 6, none, none, none, none, none, some 6, none, none, some 3, none, none, none, none, none, none, none, none, none, some 14, none, none, none, none],none,2,![none, none, none, none, none, none, some 133, none, none, none, none, none, none, none, none],![23, 10, 10, 23, 10, 10, 0, 10, 10, 23, 10, 10, 23, 10, 10]⟩

private def node133 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, none, some 6, none, none, none, none, none, some 6, none, none, some 3, none, none, none, none, none, none, none, none, none, some 14, none, none, none, none],none,6,![none, none, none, none, none, none, none, none, none, some 134, none, none, none, none, none],![10, 23, 10, 10, 23, 10, 13, 10, 10, 0, 10, 10, 13, 10, 10]⟩

private def node134 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, none, some 6, none, some 9, none, none, none, some 6, none, none, some 3, none, none, none, none, none, none, none, none, none, some 14, none, none, none, none],none,7,![none, none, none, some 135, none, none, none, none, none, none, none, none, none, none, none],![6, 2, 2, 0, 2, 2, 6, 2, 2, 2, 2, 4, 2, 2, 4]⟩

private def node135 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, none, some 6, none, some 9, some 3, none, none, some 6, none, none, some 3, none, none, none, none, none, none, none, none, none, some 14, none, none, none, none],none,8,![none, none, none, some 136, none, none, none, none, none, none, none, none, none, none, none],![6, 1, 1, 0, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 4]⟩

private def node136 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, none, some 6, none, some 9, some 3, some 3, none, some 6, none, none, some 3, none, none, none, none, none, none, none, none, none, some 14, none, none, none, none],none,9,![none, none, none, none, none, none, some 137, none, none, none, none, none, none, none, none],![6, 1, 1, 6, 1, 1, 0, 1, 1, 1, 1, 2, 1, 1, 2]⟩

private def node137 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, none, some 6, none, some 9, some 3, some 3, some 6, some 6, none, none, some 3, none, none, none, none, none, none, none, none, none, some 14, none, none, none, none],none,5,![none, none, none, none, none, none, none, none, none, some 138, none, none, none, none, none],![7, 9, 7, 7, 9, 7, 7, 7, 8, 0, 7, 7, 7, 8, 7]⟩

private def node138 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, none, some 6, some 9, some 9, some 3, some 3, some 6, some 6, none, none, some 3, none, none, none, none, none, none, none, none, none, some 14, none, none, none, none],none,11,![none, none, none, none, none, none, some 139, none, none, none, none, none, none, none, none],![4, 1, 1, 4, 1, 1, 0, 1, 1, 1, 1, 2, 1, 1, 2]⟩

private def node139 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, none, some 6, some 9, some 9, some 3, some 3, some 6, some 6, some 6, none, some 3, none, none, none, none, none, none, none, none, none, some 14, none, none, none, none],none,3,![none, none, none, none, none, none, some 140, none, none, none, none, none, none, none, none],![11, 7, 7, 11, 7, 7, 0, 7, 7, 7, 7, 8, 7, 7, 8]⟩

private def node140 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, some 6, some 6, some 9, some 9, some 3, some 3, some 6, some 6, some 6, none, some 3, none, none, none, none, none, none, none, none, none, some 14, none, none, none, none],none,12,![none, none, none, none, none, none, some 141, none, none, none, none, none, none, none, none],![4, 1, 1, 4, 1, 1, 0, 1, 1, 1, 1, 2, 1, 1, 2]⟩

private def node141 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, some 6, some 6, some 9, some 9, some 3, some 3, some 6, some 6, some 6, some 6, some 3, none, none, none, none, none, none, none, none, none, some 14, none, none, none, none],none,14,![none, none, none, some 142, none, none, none, none, none, none, none, none, none, none, none],![5, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 2, 0, 0, 2]⟩

private def node142 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, some 6, some 6, some 9, some 9, some 3, some 3, some 6, some 6, some 6, some 6, some 3, some 3, none, none, none, none, none, none, none, none, some 14, none, none, none, none],none,15,![none, none, none, none, none, none, some 143, none, none, none, none, none, none, none, none],![5, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2]⟩

private def node143 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, some 6, some 6, some 9, some 9, some 3, some 3, some 6, some 6, some 6, some 6, some 3, some 3, some 6, none, none, none, none, none, none, none, some 14, none, none, none, none],none,16,![none, none, none, none, none, none, none, some 144, none, none, none, none, none, none, none],![0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0]⟩

private def node144 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, some 6, some 6, some 9, some 9, some 3, some 3, some 6, some 6, some 6, some 6, some 3, some 3, some 6, some 7, none, none, none, none, none, none, some 14, none, none, none, none],none,17,![none, none, none, none, none, none, none, some 145, none, none, none, none, none, none, none],![0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0]⟩

private def node145 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, some 6, some 6, some 9, some 9, some 3, some 3, some 6, some 6, some 6, some 6, some 3, some 3, some 6, some 7, some 7, none, none, none, none, none, some 14, none, none, none, none],none,18,![none, none, none, some 146, none, none, none, none, none, none, none, none, none, none, none],![5, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node146 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, some 6, some 6, some 9, some 9, some 3, some 3, some 6, some 6, some 6, some 6, some 3, some 3, some 6, some 7, some 7, some 3, none, none, none, none, some 14, none, none, none, none],none,19,![none, none, none, none, none, none, some 147, none, none, none, none, none, none, none, none],![5, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node147 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, some 6, some 6, some 9, some 9, some 3, some 3, some 6, some 6, some 6, some 6, some 3, some 3, some 6, some 7, some 7, some 3, some 6, none, none, none, some 14, none, none, none, none],none,20,![none, none, none, none, none, none, none, some 148, none, none, none, none, none, none, none],![0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0]⟩

private def node148 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, some 6, some 6, some 9, some 9, some 3, some 3, some 6, some 6, some 6, some 6, some 3, some 3, some 6, some 7, some 7, some 3, some 6, some 7, none, none, some 14, none, none, none, none],none,21,![none, none, none, none, none, none, none, some 149, none, none, none, none, none, none, none],![0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0]⟩

private def node149 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, some 6, some 6, some 9, some 9, some 3, some 3, some 6, some 6, some 6, some 6, some 3, some 3, some 6, some 7, some 7, some 3, some 6, some 7, some 7, none, some 14, none, none, none, none],none,22,![some 150, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 5, 0, 0, 5, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node150 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, some 6, some 6, some 9, some 9, some 3, some 3, some 6, some 6, some 6, some 6, some 3, some 3, some 6, some 7, some 7, some 3, some 6, some 7, some 7, some 0, some 14, none, none, none, none],none,24,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 151],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]⟩

private def node151 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, some 6, some 6, some 9, some 9, some 3, some 3, some 6, some 6, some 6, some 6, some 3, some 3, some 6, some 7, some 7, some 3, some 6, some 7, some 7, some 0, some 14, some 14, none, none, none],none,25,![none, none, none, none, none, none, none, none, none, none, none, some 152, none, none, none],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]⟩

private def node152 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, some 6, some 6, some 9, some 9, some 3, some 3, some 6, some 6, some 6, some 6, some 3, some 3, some 6, some 7, some 7, some 3, some 6, some 7, some 7, some 0, some 14, some 14, some 11, none, none],none,26,![none, none, none, none, none, none, none, none, none, none, none, some 153, none, none, none],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]⟩

private def node153 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, some 6, some 6, some 9, some 9, some 3, some 3, some 6, some 6, some 6, some 6, some 3, some 3, some 6, some 7, some 7, some 3, some 6, some 7, some 7, some 0, some 14, some 14, some 11, some 11, none],none,27,![none, none, none, none, none, none, none, none, none, none, none, some 154, none, none, none],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]⟩

private def node154 : SearchNode 236 9 :=
  ⟨![some 0, some 6, some 6, some 6, some 6, some 9, some 9, some 3, some 3, some 6, some 6, some 6, some 6, some 3, some 3, some 6, some 7, some 7, some 3, some 6, some 7, some 7, some 0, some 14, some 14, some 11, some 11, some 11],some 5,0,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

private def node155 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, none, none, none, none, none, none, none, none, some 6, none, none, none, none, none, none, none, none, none, none, none, none, none, none],none,23,![none, none, none, none, none, none, none, none, none, none, none, some 156, none, none, none],![13, 0, 0, 13, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 13]⟩

private def node156 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, none, none, none, none, none, none, none, none, some 6, none, none, none, none, none, none, none, none, none, some 11, none, none, none, none],none,4,![none, none, none, none, none, none, some 157, none, none, none, none, none, none, none, none],![23, 13, 13, 23, 13, 13, 0, 23, 23, 13, 13, 13, 13, 13, 13]⟩

private def node157 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, some 6, none, none, none, none, none, none, none, none, some 6, none, none, none, none, none, none, none, none, none, some 11, none, none, none, none],none,6,![none, none, none, none, none, none, some 158, none, none, none, none, none, none, none, none],![23, 13, 13, 23, 13, 13, 0, 23, 23, 13, 13, 13, 13, 13, 13]⟩

private def node158 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, some 6, none, some 6, none, none, none, none, none, none, some 6, none, none, none, none, none, none, none, none, none, some 11, none, none, none, none],none,7,![none, none, none, none, none, none, some 159, none, none, none, none, none, none, none, none],![6, 4, 4, 6, 4, 4, 0, 4, 4, 23, 4, 4, 23, 4, 4]⟩

private def node159 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, some 6, none, some 6, some 6, none, none, none, none, none, some 6, none, none, none, none, none, none, none, none, none, some 11, none, none, none, none],none,8,![none, none, none, none, none, none, some 160, none, none, none, none, none, none, none, none],![6, 4, 4, 6, 4, 4, 0, 4, 4, 23, 4, 4, 23, 4, 4]⟩

private def node160 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, some 6, none, some 6, some 6, some 6, none, none, none, none, some 6, none, none, none, none, none, none, none, none, none, some 11, none, none, none, none],none,9,![none, none, none, none, none, none, some 161, none, none, none, none, none, none, none, none],![6, 4, 4, 6, 4, 4, 0, 4, 4, 13, 4, 4, 13, 4, 4]⟩

private def node161 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, some 6, none, some 6, some 6, some 6, some 6, none, none, none, some 6, none, none, none, none, none, none, none, none, none, some 11, none, none, none, none],none,1,![none, none, none, some 162, none, none, none, none, none, none, none, none, none, none, none],![23, 8, 8, 0, 8, 8, 23, 8, 8, 8, 8, 9, 8, 8, 9]⟩

private def node162 : SearchNode 236 9 :=
  ⟨![some 0, some 3, none, none, some 6, none, some 6, some 6, some 6, some 6, none, none, none, some 6, none, none, none, none, none, none, none, none, none, some 11, none, none, none, none],none,2,![none, none, none, some 163, none, none, none, none, none, none, none, none, none, none, none],![23, 7, 7, 0, 7, 7, 23, 7, 7, 7, 7, 9, 7, 7, 9]⟩

private def node163 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, none, some 6, none, some 6, some 6, some 6, some 6, none, none, none, some 6, none, none, none, none, none, none, none, none, none, some 11, none, none, none, none],none,10,![none, none, none, none, none, none, some 164, none, none, none, none, none, none, none, none],![6, 1, 1, 6, 1, 1, 0, 1, 1, 1, 1, 2, 1, 1, 2]⟩

private def node164 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, none, some 6, none, some 6, some 6, some 6, some 6, some 6, none, none, some 6, none, none, none, none, none, none, none, none, none, some 11, none, none, none, none],none,5,![none, none, none, none, none, none, some 165, none, none, none, none, none, none, none, none],![10, 7, 7, 10, 7, 7, 0, 7, 7, 7, 7, 8, 7, 7, 8]⟩

private def node165 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, none, some 6, some 6, some 6, some 6, some 6, some 6, some 6, none, none, some 6, none, none, none, none, none, none, none, none, none, some 11, none, none, none, none],none,11,![none, none, none, none, none, none, none, none, none, some 166, none, none, none, none, none],![1, 6, 1, 1, 6, 1, 1, 1, 2, 0, 1, 1, 1, 2, 1]⟩

private def node166 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, none, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 9, none, some 6, none, none, none, none, none, none, none, none, none, some 11, none, none, none, none],none,3,![none, none, none, none, none, none, some 167, none, none, none, none, none, none, none, none],![11, 7, 7, 11, 7, 7, 0, 7, 7, 7, 7, 8, 7, 7, 8]⟩

private def node167 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 9, none, some 6, none, none, none, none, none, none, none, none, none, some 11, none, none, none, none],none,12,![none, none, none, none, none, none, none, none, none, some 168, none, none, none, none, none],![1, 3, 1, 1, 3, 1, 1, 1, 2, 0, 1, 1, 1, 2, 1]⟩

private def node168 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 9, some 9, some 6, none, none, none, none, none, none, none, none, none, some 11, none, none, none, none],none,14,![none, none, none, none, none, none, some 169, none, none, none, none, none, none, none, none],![5, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2]⟩

private def node169 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 9, some 9, some 6, some 6, none, none, none, none, none, none, none, none, some 11, none, none, none, none],none,15,![none, none, none, some 170, none, none, none, none, none, none, none, none, none, none, none],![5, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 2, 0, 0, 2]⟩

private def node170 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 9, some 9, some 6, some 6, some 3, none, none, none, none, none, none, none, some 11, none, none, none, none],none,16,![none, none, none, none, none, none, none, none, none, none, some 171, none, none, none, none],![0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0]⟩

private def node171 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 9, some 9, some 6, some 6, some 3, some 10, none, none, none, none, none, none, some 11, none, none, none, none],none,17,![none, none, none, none, none, none, none, none, none, none, some 172, none, none, none, none],![0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0]⟩

private def node172 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 9, some 9, some 6, some 6, some 3, some 10, some 10, none, none, none, none, none, some 11, none, none, none, none],none,18,![none, none, none, none, none, none, some 173, none, none, none, none, none, none, none, none],![5, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node173 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 9, some 9, some 6, some 6, some 3, some 10, some 10, some 6, none, none, none, none, some 11, none, none, none, none],none,19,![none, none, none, some 174, none, none, none, none, none, none, none, none, none, none, none],![5, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node174 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 9, some 9, some 6, some 6, some 3, some 10, some 10, some 6, some 3, none, none, none, some 11, none, none, none, none],none,20,![none, none, none, none, none, none, none, none, none, none, some 175, none, none, none, none],![0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0]⟩

private def node175 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 9, some 9, some 6, some 6, some 3, some 10, some 10, some 6, some 3, some 10, none, none, some 11, none, none, none, none],none,21,![none, none, none, none, none, none, none, none, none, none, some 176, none, none, none, none],![0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0]⟩

private def node176 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 9, some 9, some 6, some 6, some 3, some 10, some 10, some 6, some 3, some 10, some 10, none, some 11, none, none, none, none],none,22,![some 177, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 5, 0, 0, 5, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node177 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 9, some 9, some 6, some 6, some 3, some 10, some 10, some 6, some 3, some 10, some 10, some 0, some 11, none, none, none, none],none,24,![none, none, none, none, none, none, none, none, none, none, none, some 178, none, none, none],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]⟩

private def node178 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 9, some 9, some 6, some 6, some 3, some 10, some 10, some 6, some 3, some 10, some 10, some 0, some 11, some 11, none, none, none],none,25,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 179],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]⟩

private def node179 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 9, some 9, some 6, some 6, some 3, some 10, some 10, some 6, some 3, some 10, some 10, some 0, some 11, some 11, some 14, none, none],none,26,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 180],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]⟩

private def node180 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 9, some 9, some 6, some 6, some 3, some 10, some 10, some 6, some 3, some 10, some 10, some 0, some 11, some 11, some 14, some 14, none],none,27,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 181],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]⟩

private def node181 : SearchNode 236 9 :=
  ⟨![some 0, some 3, some 3, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 6, some 9, some 9, some 6, some 6, some 3, some 10, some 10, some 6, some 3, some 10, some 10, some 0, some 11, some 11, some 14, some 14, some 14],some 6,0,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

private def node182 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, none, none, none, none, none, none, none, none, some 11, none, none, none, none, none, none, none, none, none, none, none, none, none, none],none,22,![none, none, none, none, none, none, none, none, none, none, none, some 183, none, none, none],![13, 0, 0, 13, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 13]⟩

private def node183 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, none, none, none, none, none, none, none, none, some 11, none, none, none, none, none, none, none, none, some 11, none, none, none, none, none],none,16,![none, none, none, none, none, some 184, none, none, none, none, none, none, none, none, none],![0, 0, 22, 0, 0, 0, 0, 22, 0, 0, 22, 0, 22, 0, 0]⟩

private def node184 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, none, none, none, none, none, none, none, none, some 11, none, none, some 5, none, none, none, none, none, some 11, none, none, none, none, none],none,6,![none, none, none, none, none, none, none, none, none, none, none, none, some 185, none, none],![13, 13, 22, 13, 13, 22, 13, 13, 13, 13, 13, 13, 0, 16, 16]⟩

private def node185 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, none, some 12, none, none, none, none, none, none, some 11, none, none, some 5, none, none, none, none, none, some 11, none, none, none, none, none],none,7,![none, none, none, none, none, none, none, none, none, none, none, some 186, none, none, none],![22, 6, 6, 6, 22, 6, 6, 22, 6, 6, 6, 0, 6, 6, 22]⟩

private def node186 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, none, some 12, some 11, none, none, none, none, none, some 11, none, none, some 5, none, none, none, none, none, some 11, none, none, none, none, none],none,2,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 187],![22, 7, 7, 16, 7, 7, 16, 7, 7, 7, 7, 22, 7, 7, 0]⟩

private def node187 : SearchNode 236 9 :=
  ⟨![some 0, none, some 14, none, none, none, some 12, some 11, none, none, none, none, none, some 11, none, none, some 5, none, none, none, none, none, some 11, none, none, none, none, none],none,3,![none, none, none, none, none, none, none, none, none, none, none, none, some 188, none, none],![7, 7, 16, 7, 7, 16, 7, 13, 7, 7, 13, 7, 0, 7, 7]⟩

private def node188 : SearchNode 236 9 :=
  ⟨![some 0, none, some 14, some 12, none, none, some 12, some 11, none, none, none, none, none, some 11, none, none, some 5, none, none, none, none, none, some 11, none, none, none, none, none],none,4,![none, none, none, none, none, none, none, none, none, none, none, none, some 189, none, none],![7, 7, 16, 7, 7, 16, 7, 13, 7, 7, 13, 7, 0, 7, 7]⟩

private def node189 : SearchNode 236 9 :=
  ⟨![some 0, none, some 14, some 12, some 12, none, some 12, some 11, none, none, none, none, none, some 11, none, none, some 5, none, none, none, none, none, some 11, none, none, none, none, none],none,5,![none, none, none, none, none, none, none, none, none, none, none, none, some 190, none, none],![7, 7, 22, 7, 7, 22, 7, 13, 7, 7, 13, 7, 0, 7, 7]⟩

private def node190 : SearchNode 236 9 :=
  ⟨![some 0, none, some 14, some 12, some 12, some 12, some 12, some 11, none, none, none, none, none, some 11, none, none, some 5, none, none, none, none, none, some 11, none, none, none, none, none],none,8,![none, none, none, none, none, none, none, none, none, none, none, some 191, none, none, none],![3, 3, 4, 3, 3, 6, 3, 3, 6, 3, 3, 0, 4, 3, 3]⟩

private def node191 : SearchNode 236 9 :=
  ⟨![some 0, none, some 14, some 12, some 12, some 12, some 12, some 11, some 11, none, none, none, none, some 11, none, none, some 5, none, none, none, none, none, some 11, none, none, none, none, none],none,1,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 192],![22, 8, 8, 22, 8, 8, 22, 8, 8, 8, 8, 22, 8, 8, 0]⟩

private def node192 : SearchNode 236 9 :=
  ⟨![some 0, some 14, some 14, some 12, some 12, some 12, some 12, some 11, some 11, none, none, none, none, some 11, none, none, some 5, none, none, none, none, none, some 11, none, none, none, none, none],none,9,![none, none, none, none, none, none, none, none, none, some 193, none, none, none, none, none],![1, 4, 1, 1, 4, 1, 1, 1, 2, 0, 1, 1, 1, 2, 1]⟩

private def node193 : SearchNode 236 9 :=
  ⟨![some 0, some 14, some 14, some 12, some 12, some 12, some 12, some 11, some 11, some 9, none, none, none, some 11, none, none, some 5, none, none, none, none, none, some 11, none, none, none, none, none],none,10,![none, none, none, none, none, none, none, none, none, some 194, none, none, none, none, none],![1, 3, 1, 1, 3, 1, 1, 1, 2, 0, 1, 1, 1, 2, 1]⟩

private def node194 : SearchNode 236 9 :=
  ⟨![some 0, some 14, some 14, some 12, some 12, some 12, some 12, some 11, some 11, some 9, some 9, none, none, some 11, none, none, some 5, none, none, none, none, none, some 11, none, none, none, none, none],none,11,![none, none, none, none, none, none, none, none, none, none, none, none, some 195, none, none],![1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 1, 0, 1, 1]⟩

private def node195 : SearchNode 236 9 :=
  ⟨![some 0, some 14, some 14, some 12, some 12, some 12, some 12, some 11, some 11, some 9, some 9, some 12, none, some 11, none, none, some 5, none, none, none, none, none, some 11, none, none, none, none, none],none,12,![none, none, none, none, none, none, none, none, none, none, none, none, some 196, none, none],![1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 1, 0, 1, 1]⟩

private def node196 : SearchNode 236 9 :=
  ⟨![some 0, some 14, some 14, some 12, some 12, some 12, some 12, some 11, some 11, some 9, some 9, some 12, some 12, some 11, none, none, some 5, none, none, none, none, none, some 11, none, none, none, none, none],none,14,![none, none, none, none, none, none, none, none, none, none, none, some 197, none, none, none],![2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2]⟩

private def node197 : SearchNode 236 9 :=
  ⟨![some 0, some 14, some 14, some 12, some 12, some 12, some 12, some 11, some 11, some 9, some 9, some 12, some 12, some 11, some 11, none, some 5, none, none, none, none, none, some 11, none, none, none, none, none],none,15,![none, none, none, none, none, none, none, none, none, none, none, some 198, none, none, none],![2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2]⟩

private def node198 : SearchNode 236 9 :=
  ⟨![some 0, some 14, some 14, some 12, some 12, some 12, some 12, some 11, some 11, some 9, some 9, some 12, some 12, some 11, some 11, some 11, some 5, none, none, none, none, none, some 11, none, none, none, none, none],none,17,![none, none, none, none, none, none, none, none, none, none, none, none, some 199, none, none],![0, 0, 3, 0, 0, 3, 0, 2, 0, 0, 2, 0, 0, 0, 0]⟩

private def node199 : SearchNode 236 9 :=
  ⟨![some 0, some 14, some 14, some 12, some 12, some 12, some 12, some 11, some 11, some 9, some 9, some 12, some 12, some 11, some 11, some 11, some 5, some 12, none, none, none, none, some 11, none, none, none, none, none],none,18,![none, none, none, none, none, none, none, none, none, none, none, some 200, none, none, none],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]⟩

private def node200 : SearchNode 236 9 :=
  ⟨![some 0, some 14, some 14, some 12, some 12, some 12, some 12, some 11, some 11, some 9, some 9, some 12, some 12, some 11, some 11, some 11, some 5, some 12, some 11, none, none, none, some 11, none, none, none, none, none],none,19,![none, none, none, none, none, none, none, none, none, none, none, some 201, none, none, none],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]⟩

private def node201 : SearchNode 236 9 :=
  ⟨![some 0, some 14, some 14, some 12, some 12, some 12, some 12, some 11, some 11, some 9, some 9, some 12, some 12, some 11, some 11, some 11, some 5, some 12, some 11, some 11, none, none, some 11, none, none, none, none, none],none,20,![none, none, none, none, none, some 202, none, none, none, none, none, none, none, none, none],![0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 1, 0, 3, 0, 0]⟩

private def node202 : SearchNode 236 9 :=
  ⟨![some 0, some 14, some 14, some 12, some 12, some 12, some 12, some 11, some 11, some 9, some 9, some 12, some 12, some 11, some 11, some 11, some 5, some 12, some 11, some 11, some 5, none, some 11, none, none, none, none, none],none,21,![none, none, none, none, none, none, none, none, none, none, none, none, some 203, none, none],![0, 0, 3, 0, 0, 3, 0, 1, 0, 0, 1, 0, 0, 0, 0]⟩

private def node203 : SearchNode 236 9 :=
  ⟨![some 0, some 14, some 14, some 12, some 12, some 12, some 12, some 11, some 11, some 9, some 9, some 12, some 12, some 11, some 11, some 11, some 5, some 12, some 11, some 11, some 5, some 12, some 11, none, none, none, none, none],none,23,![none, none, none, none, none, none, none, none, none, none, none, some 204, none, none, none],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]⟩

private def node204 : SearchNode 236 9 :=
  ⟨![some 0, some 14, some 14, some 12, some 12, some 12, some 12, some 11, some 11, some 9, some 9, some 12, some 12, some 11, some 11, some 11, some 5, some 12, some 11, some 11, some 5, some 12, some 11, some 11, none, none, none, none],none,24,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 205],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]⟩

private def node205 : SearchNode 236 9 :=
  ⟨![some 0, some 14, some 14, some 12, some 12, some 12, some 12, some 11, some 11, some 9, some 9, some 12, some 12, some 11, some 11, some 11, some 5, some 12, some 11, some 11, some 5, some 12, some 11, some 11, some 14, none, none, none],none,25,![none, none, none, none, none, none, none, none, none, none, none, some 206, none, none, none],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]⟩

private def node206 : SearchNode 236 9 :=
  ⟨![some 0, some 14, some 14, some 12, some 12, some 12, some 12, some 11, some 11, some 9, some 9, some 12, some 12, some 11, some 11, some 11, some 5, some 12, some 11, some 11, some 5, some 12, some 11, some 11, some 14, some 11, none, none],none,26,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 207],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]⟩

private def node207 : SearchNode 236 9 :=
  ⟨![some 0, some 14, some 14, some 12, some 12, some 12, some 12, some 11, some 11, some 9, some 9, some 12, some 12, some 11, some 11, some 11, some 5, some 12, some 11, some 11, some 5, some 12, some 11, some 11, some 14, some 11, some 14, none],none,27,![some 208, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node208 : SearchNode 236 9 :=
  ⟨![some 0, some 14, some 14, some 12, some 12, some 12, some 12, some 11, some 11, some 9, some 9, some 12, some 12, some 11, some 11, some 11, some 5, some 12, some 11, some 11, some 5, some 12, some 11, some 11, some 14, some 11, some 14, some 0],some 7,0,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

private def node209 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, none, none, none, none, none, none, none, none, some 14, none, none, none, none, none, none, none, none, none, none, none, none, none, none],none,22,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 210],![13, 0, 0, 13, 0, 0, 13, 0, 0, 0, 0, 13, 0, 0, 0]⟩

private def node210 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, none, none, none, none, none, none, none, none, some 14, none, none, none, none, none, none, none, none, some 14, none, none, none, none, none],none,16,![none, none, none, none, none, none, none, none, none, none, none, none, some 211, none, none],![0, 0, 22, 0, 0, 22, 0, 22, 0, 0, 22, 0, 0, 0, 0]⟩

private def node211 : SearchNode 236 9 :=
  ⟨![some 0, none, none, none, none, none, none, none, none, none, none, none, none, some 14, none, none, some 12, none, none, none, none, none, some 14, none, none, none, none, none],none,2,![none, none, none, none, none, none, none, none, none, none, none, some 212, none, none, none],![22, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 0, 22, 22, 22]⟩

private def node212 : SearchNode 236 9 :=
  ⟨![some 0, none, some 11, none, none, none, none, none, none, none, none, none, none, some 14, none, none, some 12, none, none, none, none, none, some 14, none, none, none, none, none],none,6,![none, none, none, none, none, none, none, none, none, none, none, none, some 213, none, none],![13, 13, 22, 13, 13, 22, 13, 13, 13, 13, 13, 13, 0, 16, 16]⟩

private def node213 : SearchNode 236 9 :=
  ⟨![some 0, none, some 11, none, none, none, some 12, none, none, none, none, none, none, some 14, none, none, some 12, none, none, none, none, none, some 14, none, none, none, none, none],none,7,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 214],![22, 2, 2, 6, 2, 2, 6, 2, 2, 2, 2, 22, 2, 2, 0]⟩

private def node214 : SearchNode 236 9 :=
  ⟨![some 0, none, some 11, none, none, none, some 12, some 14, none, none, none, none, none, some 14, none, none, some 12, none, none, none, none, none, some 14, none, none, none, none, none],none,5,![none, none, none, none, none, none, none, none, none, none, none, none, some 215, none, none],![7, 7, 22, 7, 7, 22, 7, 13, 7, 7, 13, 7, 0, 7, 7]⟩

private def node215 : SearchNode 236 9 :=
  ⟨![some 0, none, some 11, none, none, some 12, some 12, some 14, none, none, none, none, none, some 14, none, none, some 12, none, none, none, none, none, some 14, none, none, none, none, none],none,8,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 216],![22, 5, 5, 5, 5, 6, 5, 5, 6, 5, 5, 22, 5, 5, 0]⟩

private def node216 : SearchNode 236 9 :=
  ⟨![some 0, none, some 11, none, none, some 12, some 12, some 14, some 14, none, none, none, none, some 14, none, none, some 12, none, none, none, none, none, some 14, none, none, none, none, none],none,1,![none, none, none, none, none, none, none, none, none, none, none, some 217, none, none, none],![22, 8, 8, 22, 8, 8, 22, 8, 8, 8, 8, 0, 8, 8, 22]⟩

private def node217 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, none, none, some 12, some 12, some 14, some 14, none, none, none, none, some 14, none, none, some 12, none, none, none, none, none, some 14, none, none, none, none, none],none,9,![none, none, none, none, none, none, none, none, none, none, none, none, some 218, none, none],![1, 1, 5, 1, 1, 5, 1, 2, 1, 1, 2, 1, 0, 1, 1]⟩

private def node218 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, none, none, some 12, some 12, some 14, some 14, some 12, none, none, none, some 14, none, none, some 12, none, none, none, none, none, some 14, none, none, none, none, none],none,4,![none, none, none, none, none, none, none, none, none, some 219, none, none, none, none, none],![7, 9, 7, 7, 9, 7, 7, 7, 8, 0, 7, 7, 7, 8, 7]⟩

private def node219 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, none, some 9, some 12, some 12, some 14, some 14, some 12, none, none, none, some 14, none, none, some 12, none, none, none, none, none, some 14, none, none, none, none, none],none,10,![none, none, none, none, none, none, none, none, none, none, none, none, some 220, none, none],![1, 1, 5, 1, 1, 5, 1, 2, 1, 1, 2, 1, 0, 1, 1]⟩

private def node220 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, none, some 9, some 12, some 12, some 14, some 14, some 12, some 12, none, none, some 14, none, none, some 12, none, none, none, none, none, some 14, none, none, none, none, none],none,3,![none, none, none, none, none, none, none, none, none, some 221, none, none, none, none, none],![7, 10, 7, 7, 10, 7, 7, 7, 8, 0, 7, 7, 7, 8, 7]⟩

private def node221 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, some 9, some 9, some 12, some 12, some 14, some 14, some 12, some 12, none, none, some 14, none, none, some 12, none, none, none, none, none, some 14, none, none, none, none, none],none,11,![none, none, none, none, none, none, none, none, none, none, none, none, some 222, none, none],![1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 1, 0, 1, 1]⟩

private def node222 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, some 9, some 9, some 12, some 12, some 14, some 14, some 12, some 12, some 12, none, some 14, none, none, some 12, none, none, none, none, none, some 14, none, none, none, none, none],none,12,![none, none, none, none, none, none, none, none, none, none, none, none, some 223, none, none],![1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 1, 0, 1, 1]⟩

private def node223 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, some 9, some 9, some 12, some 12, some 14, some 14, some 12, some 12, some 12, some 12, some 14, none, none, some 12, none, none, none, none, none, some 14, none, none, none, none, none],none,14,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 224],![2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0]⟩

private def node224 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, some 9, some 9, some 12, some 12, some 14, some 14, some 12, some 12, some 12, some 12, some 14, some 14, none, some 12, none, none, none, none, none, some 14, none, none, none, none, none],none,15,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 225],![2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0]⟩

private def node225 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, some 9, some 9, some 12, some 12, some 14, some 14, some 12, some 12, some 12, some 12, some 14, some 14, some 14, some 12, none, none, none, none, none, some 14, none, none, none, none, none],none,17,![none, none, none, none, none, some 226, none, none, none, none, none, none, none, none, none],![0, 0, 3, 0, 0, 0, 0, 2, 0, 0, 2, 0, 3, 0, 0]⟩

private def node226 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, some 9, some 9, some 12, some 12, some 14, some 14, some 12, some 12, some 12, some 12, some 14, some 14, some 14, some 12, some 5, none, none, none, none, some 14, none, none, none, none, none],none,18,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 227],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]⟩

private def node227 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, some 9, some 9, some 12, some 12, some 14, some 14, some 12, some 12, some 12, some 12, some 14, some 14, some 14, some 12, some 5, some 14, none, none, none, some 14, none, none, none, none, none],none,19,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 228],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]⟩

private def node228 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, some 9, some 9, some 12, some 12, some 14, some 14, some 12, some 12, some 12, some 12, some 14, some 14, some 14, some 12, some 5, some 14, some 14, none, none, some 14, none, none, none, none, none],none,20,![none, none, none, none, none, none, none, none, none, none, none, none, some 229, none, none],![0, 0, 3, 0, 0, 3, 0, 1, 0, 0, 1, 0, 0, 0, 0]⟩

private def node229 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, some 9, some 9, some 12, some 12, some 14, some 14, some 12, some 12, some 12, some 12, some 14, some 14, some 14, some 12, some 5, some 14, some 14, some 12, none, some 14, none, none, none, none, none],none,21,![none, none, none, none, none, some 230, none, none, none, none, none, none, none, none, none],![0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 1, 0, 3, 0, 0]⟩

private def node230 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, some 9, some 9, some 12, some 12, some 14, some 14, some 12, some 12, some 12, some 12, some 14, some 14, some 14, some 12, some 5, some 14, some 14, some 12, some 5, some 14, none, none, none, none, none],none,23,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 231],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]⟩

private def node231 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, some 9, some 9, some 12, some 12, some 14, some 14, some 12, some 12, some 12, some 12, some 14, some 14, some 14, some 12, some 5, some 14, some 14, some 12, some 5, some 14, some 14, none, none, none, none],none,24,![none, none, none, none, none, none, none, none, none, none, none, some 232, none, none, none],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]⟩

private def node232 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, some 9, some 9, some 12, some 12, some 14, some 14, some 12, some 12, some 12, some 12, some 14, some 14, some 14, some 12, some 5, some 14, some 14, some 12, some 5, some 14, some 14, some 11, none, none, none],none,25,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 233],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]⟩

private def node233 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, some 9, some 9, some 12, some 12, some 14, some 14, some 12, some 12, some 12, some 12, some 14, some 14, some 14, some 12, some 5, some 14, some 14, some 12, some 5, some 14, some 14, some 11, some 14, none, none],none,26,![none, none, none, none, none, none, none, none, none, none, none, some 234, none, none, none],![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]⟩

private def node234 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, some 9, some 9, some 12, some 12, some 14, some 14, some 12, some 12, some 12, some 12, some 14, some 14, some 14, some 12, some 5, some 14, some 14, some 12, some 5, some 14, some 14, some 11, some 14, some 11, none],none,27,![some 235, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 1]⟩

private def node235 : SearchNode 236 9 :=
  ⟨![some 0, some 11, some 11, some 9, some 9, some 12, some 12, some 14, some 14, some 12, some 12, some 12, some 12, some 14, some 14, some 14, some 12, some 5, some 14, some 14, some 12, some 5, some 14, some 14, some 11, some 14, some 11, some 0],some 8,0,![none, none, none, none, none, none, none, none, none, none, none, none, none, none, none],![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

def atlasNodes : Fin 236 → SearchNode 236 9 :=
  ![node0, node1, node2, node3, node4, node5, node6, node7, node8, node9, node10, node11, node12, node13, node14, node15, node16, node17, node18, node19, node20, node21, node22, node23, node24, node25, node26, node27, node28, node29, node30, node31, node32, node33, node34, node35, node36, node37, node38, node39, node40, node41, node42, node43, node44, node45, node46, node47, node48, node49, node50, node51, node52, node53, node54, node55, node56, node57, node58, node59, node60, node61, node62, node63, node64, node65, node66, node67, node68, node69, node70, node71, node72, node73, node74, node75, node76, node77, node78, node79, node80, node81, node82, node83, node84, node85, node86, node87, node88, node89, node90, node91, node92, node93, node94, node95, node96, node97, node98, node99, node100, node101, node102, node103, node104, node105, node106, node107, node108, node109, node110, node111, node112, node113, node114, node115, node116, node117, node118, node119, node120, node121, node122, node123, node124, node125, node126, node127, node128, node129, node130, node131, node132, node133, node134, node135, node136, node137, node138, node139, node140, node141, node142, node143, node144, node145, node146, node147, node148, node149, node150, node151, node152, node153, node154, node155, node156, node157, node158, node159, node160, node161, node162, node163, node164, node165, node166, node167, node168, node169, node170, node171, node172, node173, node174, node175, node176, node177, node178, node179, node180, node181, node182, node183, node184, node185, node186, node187, node188, node189, node190, node191, node192, node193, node194, node195, node196, node197, node198, node199, node200, node201, node202, node203, node204, node205, node206, node207, node208, node209, node210, node211, node212, node213, node214, node215, node216, node217, node218, node219, node220, node221, node222, node223, node224, node225, node226, node227, node228, node229, node230, node231, node232, node233, node234, node235]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_0 : NodeValid atlasRows atlasNodes 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_1 : NodeValid atlasRows atlasNodes 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_2 : NodeValid atlasRows atlasNodes 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_3 : NodeValid atlasRows atlasNodes 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_4 : NodeValid atlasRows atlasNodes 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_5 : NodeValid atlasRows atlasNodes 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_6 : NodeValid atlasRows atlasNodes 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_7 : NodeValid atlasRows atlasNodes 7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_8 : NodeValid atlasRows atlasNodes 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_9 : NodeValid atlasRows atlasNodes 9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_10 : NodeValid atlasRows atlasNodes 10 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_11 : NodeValid atlasRows atlasNodes 11 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_12 : NodeValid atlasRows atlasNodes 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_13 : NodeValid atlasRows atlasNodes 13 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_14 : NodeValid atlasRows atlasNodes 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_15 : NodeValid atlasRows atlasNodes 15 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_16 : NodeValid atlasRows atlasNodes 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_17 : NodeValid atlasRows atlasNodes 17 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_18 : NodeValid atlasRows atlasNodes 18 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_19 : NodeValid atlasRows atlasNodes 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_20 : NodeValid atlasRows atlasNodes 20 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_21 : NodeValid atlasRows atlasNodes 21 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_22 : NodeValid atlasRows atlasNodes 22 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_23 : NodeValid atlasRows atlasNodes 23 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_24 : NodeValid atlasRows atlasNodes 24 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_25 : NodeValid atlasRows atlasNodes 25 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_26 : NodeValid atlasRows atlasNodes 26 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_27 : NodeValid atlasRows atlasNodes 27 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_28 : NodeValid atlasRows atlasNodes 28 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_29 : NodeValid atlasRows atlasNodes 29 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_30 : NodeValid atlasRows atlasNodes 30 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_31 : NodeValid atlasRows atlasNodes 31 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_32 : NodeValid atlasRows atlasNodes 32 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_33 : NodeValid atlasRows atlasNodes 33 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_34 : NodeValid atlasRows atlasNodes 34 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_35 : NodeValid atlasRows atlasNodes 35 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_36 : NodeValid atlasRows atlasNodes 36 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_37 : NodeValid atlasRows atlasNodes 37 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_38 : NodeValid atlasRows atlasNodes 38 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_39 : NodeValid atlasRows atlasNodes 39 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_40 : NodeValid atlasRows atlasNodes 40 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_41 : NodeValid atlasRows atlasNodes 41 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_42 : NodeValid atlasRows atlasNodes 42 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_43 : NodeValid atlasRows atlasNodes 43 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_44 : NodeValid atlasRows atlasNodes 44 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_45 : NodeValid atlasRows atlasNodes 45 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_46 : NodeValid atlasRows atlasNodes 46 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_47 : NodeValid atlasRows atlasNodes 47 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_48 : NodeValid atlasRows atlasNodes 48 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_49 : NodeValid atlasRows atlasNodes 49 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_50 : NodeValid atlasRows atlasNodes 50 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_51 : NodeValid atlasRows atlasNodes 51 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_52 : NodeValid atlasRows atlasNodes 52 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_53 : NodeValid atlasRows atlasNodes 53 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_54 : NodeValid atlasRows atlasNodes 54 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_55 : NodeValid atlasRows atlasNodes 55 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_56 : NodeValid atlasRows atlasNodes 56 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_57 : NodeValid atlasRows atlasNodes 57 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_58 : NodeValid atlasRows atlasNodes 58 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_59 : NodeValid atlasRows atlasNodes 59 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_60 : NodeValid atlasRows atlasNodes 60 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_61 : NodeValid atlasRows atlasNodes 61 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_62 : NodeValid atlasRows atlasNodes 62 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_63 : NodeValid atlasRows atlasNodes 63 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_64 : NodeValid atlasRows atlasNodes 64 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_65 : NodeValid atlasRows atlasNodes 65 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_66 : NodeValid atlasRows atlasNodes 66 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_67 : NodeValid atlasRows atlasNodes 67 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_68 : NodeValid atlasRows atlasNodes 68 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_69 : NodeValid atlasRows atlasNodes 69 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_70 : NodeValid atlasRows atlasNodes 70 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_71 : NodeValid atlasRows atlasNodes 71 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_72 : NodeValid atlasRows atlasNodes 72 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_73 : NodeValid atlasRows atlasNodes 73 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_74 : NodeValid atlasRows atlasNodes 74 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_75 : NodeValid atlasRows atlasNodes 75 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_76 : NodeValid atlasRows atlasNodes 76 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_77 : NodeValid atlasRows atlasNodes 77 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_78 : NodeValid atlasRows atlasNodes 78 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_79 : NodeValid atlasRows atlasNodes 79 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_80 : NodeValid atlasRows atlasNodes 80 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_81 : NodeValid atlasRows atlasNodes 81 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_82 : NodeValid atlasRows atlasNodes 82 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_83 : NodeValid atlasRows atlasNodes 83 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_84 : NodeValid atlasRows atlasNodes 84 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_85 : NodeValid atlasRows atlasNodes 85 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_86 : NodeValid atlasRows atlasNodes 86 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_87 : NodeValid atlasRows atlasNodes 87 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_88 : NodeValid atlasRows atlasNodes 88 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_89 : NodeValid atlasRows atlasNodes 89 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_90 : NodeValid atlasRows atlasNodes 90 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_91 : NodeValid atlasRows atlasNodes 91 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_92 : NodeValid atlasRows atlasNodes 92 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_93 : NodeValid atlasRows atlasNodes 93 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_94 : NodeValid atlasRows atlasNodes 94 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_95 : NodeValid atlasRows atlasNodes 95 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_96 : NodeValid atlasRows atlasNodes 96 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_97 : NodeValid atlasRows atlasNodes 97 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_98 : NodeValid atlasRows atlasNodes 98 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_99 : NodeValid atlasRows atlasNodes 99 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_100 : NodeValid atlasRows atlasNodes 100 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_101 : NodeValid atlasRows atlasNodes 101 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_102 : NodeValid atlasRows atlasNodes 102 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_103 : NodeValid atlasRows atlasNodes 103 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_104 : NodeValid atlasRows atlasNodes 104 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_105 : NodeValid atlasRows atlasNodes 105 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_106 : NodeValid atlasRows atlasNodes 106 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_107 : NodeValid atlasRows atlasNodes 107 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_108 : NodeValid atlasRows atlasNodes 108 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_109 : NodeValid atlasRows atlasNodes 109 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_110 : NodeValid atlasRows atlasNodes 110 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_111 : NodeValid atlasRows atlasNodes 111 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_112 : NodeValid atlasRows atlasNodes 112 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_113 : NodeValid atlasRows atlasNodes 113 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_114 : NodeValid atlasRows atlasNodes 114 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_115 : NodeValid atlasRows atlasNodes 115 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_116 : NodeValid atlasRows atlasNodes 116 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_117 : NodeValid atlasRows atlasNodes 117 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_118 : NodeValid atlasRows atlasNodes 118 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_119 : NodeValid atlasRows atlasNodes 119 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_120 : NodeValid atlasRows atlasNodes 120 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_121 : NodeValid atlasRows atlasNodes 121 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_122 : NodeValid atlasRows atlasNodes 122 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_123 : NodeValid atlasRows atlasNodes 123 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_124 : NodeValid atlasRows atlasNodes 124 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_125 : NodeValid atlasRows atlasNodes 125 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_126 : NodeValid atlasRows atlasNodes 126 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_127 : NodeValid atlasRows atlasNodes 127 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_128 : NodeValid atlasRows atlasNodes 128 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_129 : NodeValid atlasRows atlasNodes 129 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_130 : NodeValid atlasRows atlasNodes 130 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_131 : NodeValid atlasRows atlasNodes 131 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_132 : NodeValid atlasRows atlasNodes 132 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_133 : NodeValid atlasRows atlasNodes 133 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_134 : NodeValid atlasRows atlasNodes 134 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_135 : NodeValid atlasRows atlasNodes 135 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_136 : NodeValid atlasRows atlasNodes 136 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_137 : NodeValid atlasRows atlasNodes 137 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_138 : NodeValid atlasRows atlasNodes 138 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_139 : NodeValid atlasRows atlasNodes 139 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_140 : NodeValid atlasRows atlasNodes 140 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_141 : NodeValid atlasRows atlasNodes 141 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_142 : NodeValid atlasRows atlasNodes 142 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_143 : NodeValid atlasRows atlasNodes 143 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_144 : NodeValid atlasRows atlasNodes 144 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_145 : NodeValid atlasRows atlasNodes 145 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_146 : NodeValid atlasRows atlasNodes 146 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_147 : NodeValid atlasRows atlasNodes 147 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_148 : NodeValid atlasRows atlasNodes 148 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_149 : NodeValid atlasRows atlasNodes 149 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_150 : NodeValid atlasRows atlasNodes 150 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_151 : NodeValid atlasRows atlasNodes 151 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_152 : NodeValid atlasRows atlasNodes 152 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_153 : NodeValid atlasRows atlasNodes 153 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_154 : NodeValid atlasRows atlasNodes 154 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_155 : NodeValid atlasRows atlasNodes 155 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_156 : NodeValid atlasRows atlasNodes 156 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_157 : NodeValid atlasRows atlasNodes 157 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_158 : NodeValid atlasRows atlasNodes 158 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_159 : NodeValid atlasRows atlasNodes 159 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_160 : NodeValid atlasRows atlasNodes 160 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_161 : NodeValid atlasRows atlasNodes 161 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_162 : NodeValid atlasRows atlasNodes 162 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_163 : NodeValid atlasRows atlasNodes 163 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_164 : NodeValid atlasRows atlasNodes 164 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_165 : NodeValid atlasRows atlasNodes 165 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_166 : NodeValid atlasRows atlasNodes 166 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_167 : NodeValid atlasRows atlasNodes 167 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_168 : NodeValid atlasRows atlasNodes 168 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_169 : NodeValid atlasRows atlasNodes 169 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_170 : NodeValid atlasRows atlasNodes 170 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_171 : NodeValid atlasRows atlasNodes 171 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_172 : NodeValid atlasRows atlasNodes 172 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_173 : NodeValid atlasRows atlasNodes 173 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_174 : NodeValid atlasRows atlasNodes 174 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_175 : NodeValid atlasRows atlasNodes 175 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_176 : NodeValid atlasRows atlasNodes 176 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_177 : NodeValid atlasRows atlasNodes 177 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_178 : NodeValid atlasRows atlasNodes 178 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_179 : NodeValid atlasRows atlasNodes 179 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_180 : NodeValid atlasRows atlasNodes 180 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_181 : NodeValid atlasRows atlasNodes 181 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_182 : NodeValid atlasRows atlasNodes 182 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_183 : NodeValid atlasRows atlasNodes 183 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_184 : NodeValid atlasRows atlasNodes 184 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_185 : NodeValid atlasRows atlasNodes 185 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_186 : NodeValid atlasRows atlasNodes 186 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_187 : NodeValid atlasRows atlasNodes 187 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_188 : NodeValid atlasRows atlasNodes 188 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_189 : NodeValid atlasRows atlasNodes 189 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_190 : NodeValid atlasRows atlasNodes 190 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_191 : NodeValid atlasRows atlasNodes 191 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_192 : NodeValid atlasRows atlasNodes 192 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_193 : NodeValid atlasRows atlasNodes 193 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_194 : NodeValid atlasRows atlasNodes 194 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_195 : NodeValid atlasRows atlasNodes 195 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_196 : NodeValid atlasRows atlasNodes 196 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_197 : NodeValid atlasRows atlasNodes 197 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_198 : NodeValid atlasRows atlasNodes 198 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_199 : NodeValid atlasRows atlasNodes 199 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_200 : NodeValid atlasRows atlasNodes 200 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_201 : NodeValid atlasRows atlasNodes 201 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_202 : NodeValid atlasRows atlasNodes 202 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_203 : NodeValid atlasRows atlasNodes 203 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_204 : NodeValid atlasRows atlasNodes 204 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_205 : NodeValid atlasRows atlasNodes 205 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_206 : NodeValid atlasRows atlasNodes 206 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_207 : NodeValid atlasRows atlasNodes 207 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_208 : NodeValid atlasRows atlasNodes 208 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_209 : NodeValid atlasRows atlasNodes 209 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_210 : NodeValid atlasRows atlasNodes 210 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_211 : NodeValid atlasRows atlasNodes 211 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_212 : NodeValid atlasRows atlasNodes 212 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_213 : NodeValid atlasRows atlasNodes 213 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_214 : NodeValid atlasRows atlasNodes 214 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_215 : NodeValid atlasRows atlasNodes 215 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_216 : NodeValid atlasRows atlasNodes 216 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_217 : NodeValid atlasRows atlasNodes 217 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_218 : NodeValid atlasRows atlasNodes 218 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_219 : NodeValid atlasRows atlasNodes 219 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_220 : NodeValid atlasRows atlasNodes 220 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_221 : NodeValid atlasRows atlasNodes 221 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_222 : NodeValid atlasRows atlasNodes 222 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_223 : NodeValid atlasRows atlasNodes 223 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_224 : NodeValid atlasRows atlasNodes 224 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_225 : NodeValid atlasRows atlasNodes 225 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_226 : NodeValid atlasRows atlasNodes 226 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_227 : NodeValid atlasRows atlasNodes 227 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_228 : NodeValid atlasRows atlasNodes 228 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_229 : NodeValid atlasRows atlasNodes 229 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_230 : NodeValid atlasRows atlasNodes 230 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_231 : NodeValid atlasRows atlasNodes 231 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_232 : NodeValid atlasRows atlasNodes 232 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_233 : NodeValid atlasRows atlasNodes 233 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_234 : NodeValid atlasRows atlasNodes 234 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem node_valid_235 : NodeValid atlasRows atlasNodes 235 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem atlas_nodes_valid (i : Fin 236) : NodeValid atlasRows atlasNodes i := by
  fin_cases i
  · exact node_valid_0
  · exact node_valid_1
  · exact node_valid_2
  · exact node_valid_3
  · exact node_valid_4
  · exact node_valid_5
  · exact node_valid_6
  · exact node_valid_7
  · exact node_valid_8
  · exact node_valid_9
  · exact node_valid_10
  · exact node_valid_11
  · exact node_valid_12
  · exact node_valid_13
  · exact node_valid_14
  · exact node_valid_15
  · exact node_valid_16
  · exact node_valid_17
  · exact node_valid_18
  · exact node_valid_19
  · exact node_valid_20
  · exact node_valid_21
  · exact node_valid_22
  · exact node_valid_23
  · exact node_valid_24
  · exact node_valid_25
  · exact node_valid_26
  · exact node_valid_27
  · exact node_valid_28
  · exact node_valid_29
  · exact node_valid_30
  · exact node_valid_31
  · exact node_valid_32
  · exact node_valid_33
  · exact node_valid_34
  · exact node_valid_35
  · exact node_valid_36
  · exact node_valid_37
  · exact node_valid_38
  · exact node_valid_39
  · exact node_valid_40
  · exact node_valid_41
  · exact node_valid_42
  · exact node_valid_43
  · exact node_valid_44
  · exact node_valid_45
  · exact node_valid_46
  · exact node_valid_47
  · exact node_valid_48
  · exact node_valid_49
  · exact node_valid_50
  · exact node_valid_51
  · exact node_valid_52
  · exact node_valid_53
  · exact node_valid_54
  · exact node_valid_55
  · exact node_valid_56
  · exact node_valid_57
  · exact node_valid_58
  · exact node_valid_59
  · exact node_valid_60
  · exact node_valid_61
  · exact node_valid_62
  · exact node_valid_63
  · exact node_valid_64
  · exact node_valid_65
  · exact node_valid_66
  · exact node_valid_67
  · exact node_valid_68
  · exact node_valid_69
  · exact node_valid_70
  · exact node_valid_71
  · exact node_valid_72
  · exact node_valid_73
  · exact node_valid_74
  · exact node_valid_75
  · exact node_valid_76
  · exact node_valid_77
  · exact node_valid_78
  · exact node_valid_79
  · exact node_valid_80
  · exact node_valid_81
  · exact node_valid_82
  · exact node_valid_83
  · exact node_valid_84
  · exact node_valid_85
  · exact node_valid_86
  · exact node_valid_87
  · exact node_valid_88
  · exact node_valid_89
  · exact node_valid_90
  · exact node_valid_91
  · exact node_valid_92
  · exact node_valid_93
  · exact node_valid_94
  · exact node_valid_95
  · exact node_valid_96
  · exact node_valid_97
  · exact node_valid_98
  · exact node_valid_99
  · exact node_valid_100
  · exact node_valid_101
  · exact node_valid_102
  · exact node_valid_103
  · exact node_valid_104
  · exact node_valid_105
  · exact node_valid_106
  · exact node_valid_107
  · exact node_valid_108
  · exact node_valid_109
  · exact node_valid_110
  · exact node_valid_111
  · exact node_valid_112
  · exact node_valid_113
  · exact node_valid_114
  · exact node_valid_115
  · exact node_valid_116
  · exact node_valid_117
  · exact node_valid_118
  · exact node_valid_119
  · exact node_valid_120
  · exact node_valid_121
  · exact node_valid_122
  · exact node_valid_123
  · exact node_valid_124
  · exact node_valid_125
  · exact node_valid_126
  · exact node_valid_127
  · exact node_valid_128
  · exact node_valid_129
  · exact node_valid_130
  · exact node_valid_131
  · exact node_valid_132
  · exact node_valid_133
  · exact node_valid_134
  · exact node_valid_135
  · exact node_valid_136
  · exact node_valid_137
  · exact node_valid_138
  · exact node_valid_139
  · exact node_valid_140
  · exact node_valid_141
  · exact node_valid_142
  · exact node_valid_143
  · exact node_valid_144
  · exact node_valid_145
  · exact node_valid_146
  · exact node_valid_147
  · exact node_valid_148
  · exact node_valid_149
  · exact node_valid_150
  · exact node_valid_151
  · exact node_valid_152
  · exact node_valid_153
  · exact node_valid_154
  · exact node_valid_155
  · exact node_valid_156
  · exact node_valid_157
  · exact node_valid_158
  · exact node_valid_159
  · exact node_valid_160
  · exact node_valid_161
  · exact node_valid_162
  · exact node_valid_163
  · exact node_valid_164
  · exact node_valid_165
  · exact node_valid_166
  · exact node_valid_167
  · exact node_valid_168
  · exact node_valid_169
  · exact node_valid_170
  · exact node_valid_171
  · exact node_valid_172
  · exact node_valid_173
  · exact node_valid_174
  · exact node_valid_175
  · exact node_valid_176
  · exact node_valid_177
  · exact node_valid_178
  · exact node_valid_179
  · exact node_valid_180
  · exact node_valid_181
  · exact node_valid_182
  · exact node_valid_183
  · exact node_valid_184
  · exact node_valid_185
  · exact node_valid_186
  · exact node_valid_187
  · exact node_valid_188
  · exact node_valid_189
  · exact node_valid_190
  · exact node_valid_191
  · exact node_valid_192
  · exact node_valid_193
  · exact node_valid_194
  · exact node_valid_195
  · exact node_valid_196
  · exact node_valid_197
  · exact node_valid_198
  · exact node_valid_199
  · exact node_valid_200
  · exact node_valid_201
  · exact node_valid_202
  · exact node_valid_203
  · exact node_valid_204
  · exact node_valid_205
  · exact node_valid_206
  · exact node_valid_207
  · exact node_valid_208
  · exact node_valid_209
  · exact node_valid_210
  · exact node_valid_211
  · exact node_valid_212
  · exact node_valid_213
  · exact node_valid_214
  · exact node_valid_215
  · exact node_valid_216
  · exact node_valid_217
  · exact node_valid_218
  · exact node_valid_219
  · exact node_valid_220
  · exact node_valid_221
  · exact node_valid_222
  · exact node_valid_223
  · exact node_valid_224
  · exact node_valid_225
  · exact node_valid_226
  · exact node_valid_227
  · exact node_valid_228
  · exact node_valid_229
  · exact node_valid_230
  · exact node_valid_231
  · exact node_valid_232
  · exact node_valid_233
  · exact node_valid_234
  · exact node_valid_235

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem atlas_root_partial (d : PairIndex) :
    (atlasNodes 0).assigned d = if d = 0 then some 0 else none := by
  revert d
  decide +kernel

/-- Exhaustive coverage, not just successful verification of nine witnesses. -/
theorem normalized_atlas_cover (f : Deck) (hf : DeckCompatible f) (h0 : f 0 = 0) :
    ∃ r : Fin 9, f = atlasRows r := by
  apply covered_by_valid_tree atlasRows atlasNodes atlas_nodes_valid f hf 0
  intro d k hk
  rw [atlas_root_partial] at hk
  split_ifs at hk with hd
  · subst d
    have hk0 : (0 : Choice) = k := Option.some.inj hk
    exact h0.trans hk0

end Paper2.Certificates.Q8.Atlas
