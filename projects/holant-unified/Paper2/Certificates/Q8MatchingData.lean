import Paper2.Certificates.Q8MatchingCore

/-! Canonical finite encodings of genuine perfect matchings. The fifteen
six-port candidates are proved complete for fixed-point-free involutions. -/
namespace Paper2.Certificates.Q8.Atlas

def deleted : PairIndex → Port × Port := ![(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,3), (2,4), (2,5), (2,6), (2,7), (3,4), (3,5), (3,6), (3,7), (4,5), (4,6), (4,7), (5,6), (5,7), (6,7)]

def residualOrder : PairIndex → Fin 6 → Port :=
  ![![2, 3, 4, 5, 6, 7], ![1, 3, 4, 5, 6, 7], ![1, 2, 4, 5, 6, 7], ![1, 2, 3, 5, 6, 7], ![1, 2, 3, 4, 6, 7], ![1, 2, 3, 4, 5, 7], ![1, 2, 3, 4, 5, 6], ![0, 3, 4, 5, 6, 7], ![0, 2, 4, 5, 6, 7], ![0, 2, 3, 5, 6, 7], ![0, 2, 3, 4, 6, 7], ![0, 2, 3, 4, 5, 7], ![0, 2, 3, 4, 5, 6], ![0, 1, 4, 5, 6, 7], ![0, 1, 3, 5, 6, 7], ![0, 1, 3, 4, 6, 7], ![0, 1, 3, 4, 5, 7], ![0, 1, 3, 4, 5, 6], ![0, 1, 2, 5, 6, 7], ![0, 1, 2, 4, 6, 7], ![0, 1, 2, 4, 5, 7], ![0, 1, 2, 4, 5, 6], ![0, 1, 2, 3, 6, 7], ![0, 1, 2, 3, 5, 7], ![0, 1, 2, 3, 5, 6], ![0, 1, 2, 3, 4, 7], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]]

def residualIndex : PairIndex → Port → Fin 6 :=
  ![![0, 0, 0, 1, 2, 3, 4, 5], ![0, 0, 0, 1, 2, 3, 4, 5], ![0, 0, 1, 0, 2, 3, 4, 5], ![0, 0, 1, 2, 0, 3, 4, 5], ![0, 0, 1, 2, 3, 0, 4, 5], ![0, 0, 1, 2, 3, 4, 0, 5], ![0, 0, 1, 2, 3, 4, 5, 0], ![0, 0, 0, 1, 2, 3, 4, 5], ![0, 0, 1, 0, 2, 3, 4, 5], ![0, 0, 1, 2, 0, 3, 4, 5], ![0, 0, 1, 2, 3, 0, 4, 5], ![0, 0, 1, 2, 3, 4, 0, 5], ![0, 0, 1, 2, 3, 4, 5, 0], ![0, 1, 0, 0, 2, 3, 4, 5], ![0, 1, 0, 2, 0, 3, 4, 5], ![0, 1, 0, 2, 3, 0, 4, 5], ![0, 1, 0, 2, 3, 4, 0, 5], ![0, 1, 0, 2, 3, 4, 5, 0], ![0, 1, 2, 0, 0, 3, 4, 5], ![0, 1, 2, 0, 3, 0, 4, 5], ![0, 1, 2, 0, 3, 4, 0, 5], ![0, 1, 2, 0, 3, 4, 5, 0], ![0, 1, 2, 3, 0, 0, 4, 5], ![0, 1, 2, 3, 0, 4, 0, 5], ![0, 1, 2, 3, 0, 4, 5, 0], ![0, 1, 2, 3, 4, 0, 0, 5], ![0, 1, 2, 3, 4, 0, 5, 0], ![0, 1, 2, 3, 4, 5, 0, 0]]

def fullMate : PairIndex → Choice → Port → Port :=
  ![![![0, 1, 3, 2, 5, 4, 7, 6], ![0, 1, 3, 2, 6, 7, 4, 5], ![0, 1, 3, 2, 7, 6, 5, 4], ![0, 1, 4, 5, 2, 3, 7, 6], ![0, 1, 4, 6, 2, 7, 3, 5], ![0, 1, 4, 7, 2, 6, 5, 3], ![0, 1, 5, 4, 3, 2, 7, 6], ![0, 1, 5, 6, 7, 2, 3, 4], ![0, 1, 5, 7, 6, 2, 4, 3], ![0, 1, 6, 4, 3, 7, 2, 5], ![0, 1, 6, 5, 7, 3, 2, 4], ![0, 1, 6, 7, 5, 4, 2, 3], ![0, 1, 7, 4, 3, 6, 5, 2], ![0, 1, 7, 5, 6, 3, 4, 2], ![0, 1, 7, 6, 5, 4, 3, 2]], ![![0, 3, 2, 1, 5, 4, 7, 6], ![0, 3, 2, 1, 6, 7, 4, 5], ![0, 3, 2, 1, 7, 6, 5, 4], ![0, 4, 2, 5, 1, 3, 7, 6], ![0, 4, 2, 6, 1, 7, 3, 5], ![0, 4, 2, 7, 1, 6, 5, 3], ![0, 5, 2, 4, 3, 1, 7, 6], ![0, 5, 2, 6, 7, 1, 3, 4], ![0, 5, 2, 7, 6, 1, 4, 3], ![0, 6, 2, 4, 3, 7, 1, 5], ![0, 6, 2, 5, 7, 3, 1, 4], ![0, 6, 2, 7, 5, 4, 1, 3], ![0, 7, 2, 4, 3, 6, 5, 1], ![0, 7, 2, 5, 6, 3, 4, 1], ![0, 7, 2, 6, 5, 4, 3, 1]], ![![0, 2, 1, 3, 5, 4, 7, 6], ![0, 2, 1, 3, 6, 7, 4, 5], ![0, 2, 1, 3, 7, 6, 5, 4], ![0, 4, 5, 3, 1, 2, 7, 6], ![0, 4, 6, 3, 1, 7, 2, 5], ![0, 4, 7, 3, 1, 6, 5, 2], ![0, 5, 4, 3, 2, 1, 7, 6], ![0, 5, 6, 3, 7, 1, 2, 4], ![0, 5, 7, 3, 6, 1, 4, 2], ![0, 6, 4, 3, 2, 7, 1, 5], ![0, 6, 5, 3, 7, 2, 1, 4], ![0, 6, 7, 3, 5, 4, 1, 2], ![0, 7, 4, 3, 2, 6, 5, 1], ![0, 7, 5, 3, 6, 2, 4, 1], ![0, 7, 6, 3, 5, 4, 2, 1]], ![![0, 2, 1, 5, 4, 3, 7, 6], ![0, 2, 1, 6, 4, 7, 3, 5], ![0, 2, 1, 7, 4, 6, 5, 3], ![0, 3, 5, 1, 4, 2, 7, 6], ![0, 3, 6, 1, 4, 7, 2, 5], ![0, 3, 7, 1, 4, 6, 5, 2], ![0, 5, 3, 2, 4, 1, 7, 6], ![0, 5, 6, 7, 4, 1, 2, 3], ![0, 5, 7, 6, 4, 1, 3, 2], ![0, 6, 3, 2, 4, 7, 1, 5], ![0, 6, 5, 7, 4, 2, 1, 3], ![0, 6, 7, 5, 4, 3, 1, 2], ![0, 7, 3, 2, 4, 6, 5, 1], ![0, 7, 5, 6, 4, 2, 3, 1], ![0, 7, 6, 5, 4, 3, 2, 1]], ![![0, 2, 1, 4, 3, 5, 7, 6], ![0, 2, 1, 6, 7, 5, 3, 4], ![0, 2, 1, 7, 6, 5, 4, 3], ![0, 3, 4, 1, 2, 5, 7, 6], ![0, 3, 6, 1, 7, 5, 2, 4], ![0, 3, 7, 1, 6, 5, 4, 2], ![0, 4, 3, 2, 1, 5, 7, 6], ![0, 4, 6, 7, 1, 5, 2, 3], ![0, 4, 7, 6, 1, 5, 3, 2], ![0, 6, 3, 2, 7, 5, 1, 4], ![0, 6, 4, 7, 2, 5, 1, 3], ![0, 6, 7, 4, 3, 5, 1, 2], ![0, 7, 3, 2, 6, 5, 4, 1], ![0, 7, 4, 6, 2, 5, 3, 1], ![0, 7, 6, 4, 3, 5, 2, 1]], ![![0, 2, 1, 4, 3, 7, 6, 5], ![0, 2, 1, 5, 7, 3, 6, 4], ![0, 2, 1, 7, 5, 4, 6, 3], ![0, 3, 4, 1, 2, 7, 6, 5], ![0, 3, 5, 1, 7, 2, 6, 4], ![0, 3, 7, 1, 5, 4, 6, 2], ![0, 4, 3, 2, 1, 7, 6, 5], ![0, 4, 5, 7, 1, 2, 6, 3], ![0, 4, 7, 5, 1, 3, 6, 2], ![0, 5, 3, 2, 7, 1, 6, 4], ![0, 5, 4, 7, 2, 1, 6, 3], ![0, 5, 7, 4, 3, 1, 6, 2], ![0, 7, 3, 2, 5, 4, 6, 1], ![0, 7, 4, 5, 2, 3, 6, 1], ![0, 7, 5, 4, 3, 2, 6, 1]], ![![0, 2, 1, 4, 3, 6, 5, 7], ![0, 2, 1, 5, 6, 3, 4, 7], ![0, 2, 1, 6, 5, 4, 3, 7], ![0, 3, 4, 1, 2, 6, 5, 7], ![0, 3, 5, 1, 6, 2, 4, 7], ![0, 3, 6, 1, 5, 4, 2, 7], ![0, 4, 3, 2, 1, 6, 5, 7], ![0, 4, 5, 6, 1, 2, 3, 7], ![0, 4, 6, 5, 1, 3, 2, 7], ![0, 5, 3, 2, 6, 1, 4, 7], ![0, 5, 4, 6, 2, 1, 3, 7], ![0, 5, 6, 4, 3, 1, 2, 7], ![0, 6, 3, 2, 5, 4, 1, 7], ![0, 6, 4, 5, 2, 3, 1, 7], ![0, 6, 5, 4, 3, 2, 1, 7]], ![![3, 1, 2, 0, 5, 4, 7, 6], ![3, 1, 2, 0, 6, 7, 4, 5], ![3, 1, 2, 0, 7, 6, 5, 4], ![4, 1, 2, 5, 0, 3, 7, 6], ![4, 1, 2, 6, 0, 7, 3, 5], ![4, 1, 2, 7, 0, 6, 5, 3], ![5, 1, 2, 4, 3, 0, 7, 6], ![5, 1, 2, 6, 7, 0, 3, 4], ![5, 1, 2, 7, 6, 0, 4, 3], ![6, 1, 2, 4, 3, 7, 0, 5], ![6, 1, 2, 5, 7, 3, 0, 4], ![6, 1, 2, 7, 5, 4, 0, 3], ![7, 1, 2, 4, 3, 6, 5, 0], ![7, 1, 2, 5, 6, 3, 4, 0], ![7, 1, 2, 6, 5, 4, 3, 0]], ![![2, 1, 0, 3, 5, 4, 7, 6], ![2, 1, 0, 3, 6, 7, 4, 5], ![2, 1, 0, 3, 7, 6, 5, 4], ![4, 1, 5, 3, 0, 2, 7, 6], ![4, 1, 6, 3, 0, 7, 2, 5], ![4, 1, 7, 3, 0, 6, 5, 2], ![5, 1, 4, 3, 2, 0, 7, 6], ![5, 1, 6, 3, 7, 0, 2, 4], ![5, 1, 7, 3, 6, 0, 4, 2], ![6, 1, 4, 3, 2, 7, 0, 5], ![6, 1, 5, 3, 7, 2, 0, 4], ![6, 1, 7, 3, 5, 4, 0, 2], ![7, 1, 4, 3, 2, 6, 5, 0], ![7, 1, 5, 3, 6, 2, 4, 0], ![7, 1, 6, 3, 5, 4, 2, 0]], ![![2, 1, 0, 5, 4, 3, 7, 6], ![2, 1, 0, 6, 4, 7, 3, 5], ![2, 1, 0, 7, 4, 6, 5, 3], ![3, 1, 5, 0, 4, 2, 7, 6], ![3, 1, 6, 0, 4, 7, 2, 5], ![3, 1, 7, 0, 4, 6, 5, 2], ![5, 1, 3, 2, 4, 0, 7, 6], ![5, 1, 6, 7, 4, 0, 2, 3], ![5, 1, 7, 6, 4, 0, 3, 2], ![6, 1, 3, 2, 4, 7, 0, 5], ![6, 1, 5, 7, 4, 2, 0, 3], ![6, 1, 7, 5, 4, 3, 0, 2], ![7, 1, 3, 2, 4, 6, 5, 0], ![7, 1, 5, 6, 4, 2, 3, 0], ![7, 1, 6, 5, 4, 3, 2, 0]], ![![2, 1, 0, 4, 3, 5, 7, 6], ![2, 1, 0, 6, 7, 5, 3, 4], ![2, 1, 0, 7, 6, 5, 4, 3], ![3, 1, 4, 0, 2, 5, 7, 6], ![3, 1, 6, 0, 7, 5, 2, 4], ![3, 1, 7, 0, 6, 5, 4, 2], ![4, 1, 3, 2, 0, 5, 7, 6], ![4, 1, 6, 7, 0, 5, 2, 3], ![4, 1, 7, 6, 0, 5, 3, 2], ![6, 1, 3, 2, 7, 5, 0, 4], ![6, 1, 4, 7, 2, 5, 0, 3], ![6, 1, 7, 4, 3, 5, 0, 2], ![7, 1, 3, 2, 6, 5, 4, 0], ![7, 1, 4, 6, 2, 5, 3, 0], ![7, 1, 6, 4, 3, 5, 2, 0]], ![![2, 1, 0, 4, 3, 7, 6, 5], ![2, 1, 0, 5, 7, 3, 6, 4], ![2, 1, 0, 7, 5, 4, 6, 3], ![3, 1, 4, 0, 2, 7, 6, 5], ![3, 1, 5, 0, 7, 2, 6, 4], ![3, 1, 7, 0, 5, 4, 6, 2], ![4, 1, 3, 2, 0, 7, 6, 5], ![4, 1, 5, 7, 0, 2, 6, 3], ![4, 1, 7, 5, 0, 3, 6, 2], ![5, 1, 3, 2, 7, 0, 6, 4], ![5, 1, 4, 7, 2, 0, 6, 3], ![5, 1, 7, 4, 3, 0, 6, 2], ![7, 1, 3, 2, 5, 4, 6, 0], ![7, 1, 4, 5, 2, 3, 6, 0], ![7, 1, 5, 4, 3, 2, 6, 0]], ![![2, 1, 0, 4, 3, 6, 5, 7], ![2, 1, 0, 5, 6, 3, 4, 7], ![2, 1, 0, 6, 5, 4, 3, 7], ![3, 1, 4, 0, 2, 6, 5, 7], ![3, 1, 5, 0, 6, 2, 4, 7], ![3, 1, 6, 0, 5, 4, 2, 7], ![4, 1, 3, 2, 0, 6, 5, 7], ![4, 1, 5, 6, 0, 2, 3, 7], ![4, 1, 6, 5, 0, 3, 2, 7], ![5, 1, 3, 2, 6, 0, 4, 7], ![5, 1, 4, 6, 2, 0, 3, 7], ![5, 1, 6, 4, 3, 0, 2, 7], ![6, 1, 3, 2, 5, 4, 0, 7], ![6, 1, 4, 5, 2, 3, 0, 7], ![6, 1, 5, 4, 3, 2, 0, 7]], ![![1, 0, 2, 3, 5, 4, 7, 6], ![1, 0, 2, 3, 6, 7, 4, 5], ![1, 0, 2, 3, 7, 6, 5, 4], ![4, 5, 2, 3, 0, 1, 7, 6], ![4, 6, 2, 3, 0, 7, 1, 5], ![4, 7, 2, 3, 0, 6, 5, 1], ![5, 4, 2, 3, 1, 0, 7, 6], ![5, 6, 2, 3, 7, 0, 1, 4], ![5, 7, 2, 3, 6, 0, 4, 1], ![6, 4, 2, 3, 1, 7, 0, 5], ![6, 5, 2, 3, 7, 1, 0, 4], ![6, 7, 2, 3, 5, 4, 0, 1], ![7, 4, 2, 3, 1, 6, 5, 0], ![7, 5, 2, 3, 6, 1, 4, 0], ![7, 6, 2, 3, 5, 4, 1, 0]], ![![1, 0, 2, 5, 4, 3, 7, 6], ![1, 0, 2, 6, 4, 7, 3, 5], ![1, 0, 2, 7, 4, 6, 5, 3], ![3, 5, 2, 0, 4, 1, 7, 6], ![3, 6, 2, 0, 4, 7, 1, 5], ![3, 7, 2, 0, 4, 6, 5, 1], ![5, 3, 2, 1, 4, 0, 7, 6], ![5, 6, 2, 7, 4, 0, 1, 3], ![5, 7, 2, 6, 4, 0, 3, 1], ![6, 3, 2, 1, 4, 7, 0, 5], ![6, 5, 2, 7, 4, 1, 0, 3], ![6, 7, 2, 5, 4, 3, 0, 1], ![7, 3, 2, 1, 4, 6, 5, 0], ![7, 5, 2, 6, 4, 1, 3, 0], ![7, 6, 2, 5, 4, 3, 1, 0]], ![![1, 0, 2, 4, 3, 5, 7, 6], ![1, 0, 2, 6, 7, 5, 3, 4], ![1, 0, 2, 7, 6, 5, 4, 3], ![3, 4, 2, 0, 1, 5, 7, 6], ![3, 6, 2, 0, 7, 5, 1, 4], ![3, 7, 2, 0, 6, 5, 4, 1], ![4, 3, 2, 1, 0, 5, 7, 6], ![4, 6, 2, 7, 0, 5, 1, 3], ![4, 7, 2, 6, 0, 5, 3, 1], ![6, 3, 2, 1, 7, 5, 0, 4], ![6, 4, 2, 7, 1, 5, 0, 3], ![6, 7, 2, 4, 3, 5, 0, 1], ![7, 3, 2, 1, 6, 5, 4, 0], ![7, 4, 2, 6, 1, 5, 3, 0], ![7, 6, 2, 4, 3, 5, 1, 0]], ![![1, 0, 2, 4, 3, 7, 6, 5], ![1, 0, 2, 5, 7, 3, 6, 4], ![1, 0, 2, 7, 5, 4, 6, 3], ![3, 4, 2, 0, 1, 7, 6, 5], ![3, 5, 2, 0, 7, 1, 6, 4], ![3, 7, 2, 0, 5, 4, 6, 1], ![4, 3, 2, 1, 0, 7, 6, 5], ![4, 5, 2, 7, 0, 1, 6, 3], ![4, 7, 2, 5, 0, 3, 6, 1], ![5, 3, 2, 1, 7, 0, 6, 4], ![5, 4, 2, 7, 1, 0, 6, 3], ![5, 7, 2, 4, 3, 0, 6, 1], ![7, 3, 2, 1, 5, 4, 6, 0], ![7, 4, 2, 5, 1, 3, 6, 0], ![7, 5, 2, 4, 3, 1, 6, 0]], ![![1, 0, 2, 4, 3, 6, 5, 7], ![1, 0, 2, 5, 6, 3, 4, 7], ![1, 0, 2, 6, 5, 4, 3, 7], ![3, 4, 2, 0, 1, 6, 5, 7], ![3, 5, 2, 0, 6, 1, 4, 7], ![3, 6, 2, 0, 5, 4, 1, 7], ![4, 3, 2, 1, 0, 6, 5, 7], ![4, 5, 2, 6, 0, 1, 3, 7], ![4, 6, 2, 5, 0, 3, 1, 7], ![5, 3, 2, 1, 6, 0, 4, 7], ![5, 4, 2, 6, 1, 0, 3, 7], ![5, 6, 2, 4, 3, 0, 1, 7], ![6, 3, 2, 1, 5, 4, 0, 7], ![6, 4, 2, 5, 1, 3, 0, 7], ![6, 5, 2, 4, 3, 1, 0, 7]], ![![1, 0, 5, 3, 4, 2, 7, 6], ![1, 0, 6, 3, 4, 7, 2, 5], ![1, 0, 7, 3, 4, 6, 5, 2], ![2, 5, 0, 3, 4, 1, 7, 6], ![2, 6, 0, 3, 4, 7, 1, 5], ![2, 7, 0, 3, 4, 6, 5, 1], ![5, 2, 1, 3, 4, 0, 7, 6], ![5, 6, 7, 3, 4, 0, 1, 2], ![5, 7, 6, 3, 4, 0, 2, 1], ![6, 2, 1, 3, 4, 7, 0, 5], ![6, 5, 7, 3, 4, 1, 0, 2], ![6, 7, 5, 3, 4, 2, 0, 1], ![7, 2, 1, 3, 4, 6, 5, 0], ![7, 5, 6, 3, 4, 1, 2, 0], ![7, 6, 5, 3, 4, 2, 1, 0]], ![![1, 0, 4, 3, 2, 5, 7, 6], ![1, 0, 6, 3, 7, 5, 2, 4], ![1, 0, 7, 3, 6, 5, 4, 2], ![2, 4, 0, 3, 1, 5, 7, 6], ![2, 6, 0, 3, 7, 5, 1, 4], ![2, 7, 0, 3, 6, 5, 4, 1], ![4, 2, 1, 3, 0, 5, 7, 6], ![4, 6, 7, 3, 0, 5, 1, 2], ![4, 7, 6, 3, 0, 5, 2, 1], ![6, 2, 1, 3, 7, 5, 0, 4], ![6, 4, 7, 3, 1, 5, 0, 2], ![6, 7, 4, 3, 2, 5, 0, 1], ![7, 2, 1, 3, 6, 5, 4, 0], ![7, 4, 6, 3, 1, 5, 2, 0], ![7, 6, 4, 3, 2, 5, 1, 0]], ![![1, 0, 4, 3, 2, 7, 6, 5], ![1, 0, 5, 3, 7, 2, 6, 4], ![1, 0, 7, 3, 5, 4, 6, 2], ![2, 4, 0, 3, 1, 7, 6, 5], ![2, 5, 0, 3, 7, 1, 6, 4], ![2, 7, 0, 3, 5, 4, 6, 1], ![4, 2, 1, 3, 0, 7, 6, 5], ![4, 5, 7, 3, 0, 1, 6, 2], ![4, 7, 5, 3, 0, 2, 6, 1], ![5, 2, 1, 3, 7, 0, 6, 4], ![5, 4, 7, 3, 1, 0, 6, 2], ![5, 7, 4, 3, 2, 0, 6, 1], ![7, 2, 1, 3, 5, 4, 6, 0], ![7, 4, 5, 3, 1, 2, 6, 0], ![7, 5, 4, 3, 2, 1, 6, 0]], ![![1, 0, 4, 3, 2, 6, 5, 7], ![1, 0, 5, 3, 6, 2, 4, 7], ![1, 0, 6, 3, 5, 4, 2, 7], ![2, 4, 0, 3, 1, 6, 5, 7], ![2, 5, 0, 3, 6, 1, 4, 7], ![2, 6, 0, 3, 5, 4, 1, 7], ![4, 2, 1, 3, 0, 6, 5, 7], ![4, 5, 6, 3, 0, 1, 2, 7], ![4, 6, 5, 3, 0, 2, 1, 7], ![5, 2, 1, 3, 6, 0, 4, 7], ![5, 4, 6, 3, 1, 0, 2, 7], ![5, 6, 4, 3, 2, 0, 1, 7], ![6, 2, 1, 3, 5, 4, 0, 7], ![6, 4, 5, 3, 1, 2, 0, 7], ![6, 5, 4, 3, 2, 1, 0, 7]], ![![1, 0, 3, 2, 4, 5, 7, 6], ![1, 0, 6, 7, 4, 5, 2, 3], ![1, 0, 7, 6, 4, 5, 3, 2], ![2, 3, 0, 1, 4, 5, 7, 6], ![2, 6, 0, 7, 4, 5, 1, 3], ![2, 7, 0, 6, 4, 5, 3, 1], ![3, 2, 1, 0, 4, 5, 7, 6], ![3, 6, 7, 0, 4, 5, 1, 2], ![3, 7, 6, 0, 4, 5, 2, 1], ![6, 2, 1, 7, 4, 5, 0, 3], ![6, 3, 7, 1, 4, 5, 0, 2], ![6, 7, 3, 2, 4, 5, 0, 1], ![7, 2, 1, 6, 4, 5, 3, 0], ![7, 3, 6, 1, 4, 5, 2, 0], ![7, 6, 3, 2, 4, 5, 1, 0]], ![![1, 0, 3, 2, 4, 7, 6, 5], ![1, 0, 5, 7, 4, 2, 6, 3], ![1, 0, 7, 5, 4, 3, 6, 2], ![2, 3, 0, 1, 4, 7, 6, 5], ![2, 5, 0, 7, 4, 1, 6, 3], ![2, 7, 0, 5, 4, 3, 6, 1], ![3, 2, 1, 0, 4, 7, 6, 5], ![3, 5, 7, 0, 4, 1, 6, 2], ![3, 7, 5, 0, 4, 2, 6, 1], ![5, 2, 1, 7, 4, 0, 6, 3], ![5, 3, 7, 1, 4, 0, 6, 2], ![5, 7, 3, 2, 4, 0, 6, 1], ![7, 2, 1, 5, 4, 3, 6, 0], ![7, 3, 5, 1, 4, 2, 6, 0], ![7, 5, 3, 2, 4, 1, 6, 0]], ![![1, 0, 3, 2, 4, 6, 5, 7], ![1, 0, 5, 6, 4, 2, 3, 7], ![1, 0, 6, 5, 4, 3, 2, 7], ![2, 3, 0, 1, 4, 6, 5, 7], ![2, 5, 0, 6, 4, 1, 3, 7], ![2, 6, 0, 5, 4, 3, 1, 7], ![3, 2, 1, 0, 4, 6, 5, 7], ![3, 5, 6, 0, 4, 1, 2, 7], ![3, 6, 5, 0, 4, 2, 1, 7], ![5, 2, 1, 6, 4, 0, 3, 7], ![5, 3, 6, 1, 4, 0, 2, 7], ![5, 6, 3, 2, 4, 0, 1, 7], ![6, 2, 1, 5, 4, 3, 0, 7], ![6, 3, 5, 1, 4, 2, 0, 7], ![6, 5, 3, 2, 4, 1, 0, 7]], ![![1, 0, 3, 2, 7, 5, 6, 4], ![1, 0, 4, 7, 2, 5, 6, 3], ![1, 0, 7, 4, 3, 5, 6, 2], ![2, 3, 0, 1, 7, 5, 6, 4], ![2, 4, 0, 7, 1, 5, 6, 3], ![2, 7, 0, 4, 3, 5, 6, 1], ![3, 2, 1, 0, 7, 5, 6, 4], ![3, 4, 7, 0, 1, 5, 6, 2], ![3, 7, 4, 0, 2, 5, 6, 1], ![4, 2, 1, 7, 0, 5, 6, 3], ![4, 3, 7, 1, 0, 5, 6, 2], ![4, 7, 3, 2, 0, 5, 6, 1], ![7, 2, 1, 4, 3, 5, 6, 0], ![7, 3, 4, 1, 2, 5, 6, 0], ![7, 4, 3, 2, 1, 5, 6, 0]], ![![1, 0, 3, 2, 6, 5, 4, 7], ![1, 0, 4, 6, 2, 5, 3, 7], ![1, 0, 6, 4, 3, 5, 2, 7], ![2, 3, 0, 1, 6, 5, 4, 7], ![2, 4, 0, 6, 1, 5, 3, 7], ![2, 6, 0, 4, 3, 5, 1, 7], ![3, 2, 1, 0, 6, 5, 4, 7], ![3, 4, 6, 0, 1, 5, 2, 7], ![3, 6, 4, 0, 2, 5, 1, 7], ![4, 2, 1, 6, 0, 5, 3, 7], ![4, 3, 6, 1, 0, 5, 2, 7], ![4, 6, 3, 2, 0, 5, 1, 7], ![6, 2, 1, 4, 3, 5, 0, 7], ![6, 3, 4, 1, 2, 5, 0, 7], ![6, 4, 3, 2, 1, 5, 0, 7]], ![![1, 0, 3, 2, 5, 4, 6, 7], ![1, 0, 4, 5, 2, 3, 6, 7], ![1, 0, 5, 4, 3, 2, 6, 7], ![2, 3, 0, 1, 5, 4, 6, 7], ![2, 4, 0, 5, 1, 3, 6, 7], ![2, 5, 0, 4, 3, 1, 6, 7], ![3, 2, 1, 0, 5, 4, 6, 7], ![3, 4, 5, 0, 1, 2, 6, 7], ![3, 5, 4, 0, 2, 1, 6, 7], ![4, 2, 1, 5, 0, 3, 6, 7], ![4, 3, 5, 1, 0, 2, 6, 7], ![4, 5, 3, 2, 0, 1, 6, 7], ![5, 2, 1, 4, 3, 0, 6, 7], ![5, 3, 4, 1, 2, 0, 6, 7], ![5, 4, 3, 2, 1, 0, 6, 7]]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem residual_order_valid (d : PairIndex) :
    (∀ i, residualOrder d i ≠ (deleted d).1 ∧ residualOrder d i ≠ (deleted d).2) ∧
    (∀ i, residualIndex d (residualOrder d i) = i) ∧
    (∀ v, v ≠ (deleted d).1 → v ≠ (deleted d).2 → residualOrder d (residualIndex d v) = v) := by
  revert d
  decide +kernel

abbrev Remaining (d : PairIndex) := {v : Port // v ≠ (deleted d).1 ∧ v ≠ (deleted d).2}

def residualEquiv (d : PairIndex) : Fin 6 ≃ Remaining d where
  toFun i := ⟨residualOrder d i,(residual_order_valid d).1 i⟩
  invFun v := residualIndex d v.val
  left_inv i := (residual_order_valid d).2.1 i
  right_inv v := Subtype.ext ((residual_order_valid d).2.2 v.val v.property.1 v.property.2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_0 (k : Choice) :
    (∀ i, fullMate 0 k (residualOrder 0 i) = residualOrder 0 (standardMate k i)) ∧
    fullMate 0 k (deleted 0).1 = (deleted 0).1 ∧
    fullMate 0 k (deleted 0).2 = (deleted 0).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_1 (k : Choice) :
    (∀ i, fullMate 1 k (residualOrder 1 i) = residualOrder 1 (standardMate k i)) ∧
    fullMate 1 k (deleted 1).1 = (deleted 1).1 ∧
    fullMate 1 k (deleted 1).2 = (deleted 1).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_2 (k : Choice) :
    (∀ i, fullMate 2 k (residualOrder 2 i) = residualOrder 2 (standardMate k i)) ∧
    fullMate 2 k (deleted 2).1 = (deleted 2).1 ∧
    fullMate 2 k (deleted 2).2 = (deleted 2).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_3 (k : Choice) :
    (∀ i, fullMate 3 k (residualOrder 3 i) = residualOrder 3 (standardMate k i)) ∧
    fullMate 3 k (deleted 3).1 = (deleted 3).1 ∧
    fullMate 3 k (deleted 3).2 = (deleted 3).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_4 (k : Choice) :
    (∀ i, fullMate 4 k (residualOrder 4 i) = residualOrder 4 (standardMate k i)) ∧
    fullMate 4 k (deleted 4).1 = (deleted 4).1 ∧
    fullMate 4 k (deleted 4).2 = (deleted 4).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_5 (k : Choice) :
    (∀ i, fullMate 5 k (residualOrder 5 i) = residualOrder 5 (standardMate k i)) ∧
    fullMate 5 k (deleted 5).1 = (deleted 5).1 ∧
    fullMate 5 k (deleted 5).2 = (deleted 5).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_6 (k : Choice) :
    (∀ i, fullMate 6 k (residualOrder 6 i) = residualOrder 6 (standardMate k i)) ∧
    fullMate 6 k (deleted 6).1 = (deleted 6).1 ∧
    fullMate 6 k (deleted 6).2 = (deleted 6).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_7 (k : Choice) :
    (∀ i, fullMate 7 k (residualOrder 7 i) = residualOrder 7 (standardMate k i)) ∧
    fullMate 7 k (deleted 7).1 = (deleted 7).1 ∧
    fullMate 7 k (deleted 7).2 = (deleted 7).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_8 (k : Choice) :
    (∀ i, fullMate 8 k (residualOrder 8 i) = residualOrder 8 (standardMate k i)) ∧
    fullMate 8 k (deleted 8).1 = (deleted 8).1 ∧
    fullMate 8 k (deleted 8).2 = (deleted 8).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_9 (k : Choice) :
    (∀ i, fullMate 9 k (residualOrder 9 i) = residualOrder 9 (standardMate k i)) ∧
    fullMate 9 k (deleted 9).1 = (deleted 9).1 ∧
    fullMate 9 k (deleted 9).2 = (deleted 9).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_10 (k : Choice) :
    (∀ i, fullMate 10 k (residualOrder 10 i) = residualOrder 10 (standardMate k i)) ∧
    fullMate 10 k (deleted 10).1 = (deleted 10).1 ∧
    fullMate 10 k (deleted 10).2 = (deleted 10).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_11 (k : Choice) :
    (∀ i, fullMate 11 k (residualOrder 11 i) = residualOrder 11 (standardMate k i)) ∧
    fullMate 11 k (deleted 11).1 = (deleted 11).1 ∧
    fullMate 11 k (deleted 11).2 = (deleted 11).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_12 (k : Choice) :
    (∀ i, fullMate 12 k (residualOrder 12 i) = residualOrder 12 (standardMate k i)) ∧
    fullMate 12 k (deleted 12).1 = (deleted 12).1 ∧
    fullMate 12 k (deleted 12).2 = (deleted 12).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_13 (k : Choice) :
    (∀ i, fullMate 13 k (residualOrder 13 i) = residualOrder 13 (standardMate k i)) ∧
    fullMate 13 k (deleted 13).1 = (deleted 13).1 ∧
    fullMate 13 k (deleted 13).2 = (deleted 13).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_14 (k : Choice) :
    (∀ i, fullMate 14 k (residualOrder 14 i) = residualOrder 14 (standardMate k i)) ∧
    fullMate 14 k (deleted 14).1 = (deleted 14).1 ∧
    fullMate 14 k (deleted 14).2 = (deleted 14).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_15 (k : Choice) :
    (∀ i, fullMate 15 k (residualOrder 15 i) = residualOrder 15 (standardMate k i)) ∧
    fullMate 15 k (deleted 15).1 = (deleted 15).1 ∧
    fullMate 15 k (deleted 15).2 = (deleted 15).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_16 (k : Choice) :
    (∀ i, fullMate 16 k (residualOrder 16 i) = residualOrder 16 (standardMate k i)) ∧
    fullMate 16 k (deleted 16).1 = (deleted 16).1 ∧
    fullMate 16 k (deleted 16).2 = (deleted 16).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_17 (k : Choice) :
    (∀ i, fullMate 17 k (residualOrder 17 i) = residualOrder 17 (standardMate k i)) ∧
    fullMate 17 k (deleted 17).1 = (deleted 17).1 ∧
    fullMate 17 k (deleted 17).2 = (deleted 17).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_18 (k : Choice) :
    (∀ i, fullMate 18 k (residualOrder 18 i) = residualOrder 18 (standardMate k i)) ∧
    fullMate 18 k (deleted 18).1 = (deleted 18).1 ∧
    fullMate 18 k (deleted 18).2 = (deleted 18).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_19 (k : Choice) :
    (∀ i, fullMate 19 k (residualOrder 19 i) = residualOrder 19 (standardMate k i)) ∧
    fullMate 19 k (deleted 19).1 = (deleted 19).1 ∧
    fullMate 19 k (deleted 19).2 = (deleted 19).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_20 (k : Choice) :
    (∀ i, fullMate 20 k (residualOrder 20 i) = residualOrder 20 (standardMate k i)) ∧
    fullMate 20 k (deleted 20).1 = (deleted 20).1 ∧
    fullMate 20 k (deleted 20).2 = (deleted 20).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_21 (k : Choice) :
    (∀ i, fullMate 21 k (residualOrder 21 i) = residualOrder 21 (standardMate k i)) ∧
    fullMate 21 k (deleted 21).1 = (deleted 21).1 ∧
    fullMate 21 k (deleted 21).2 = (deleted 21).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_22 (k : Choice) :
    (∀ i, fullMate 22 k (residualOrder 22 i) = residualOrder 22 (standardMate k i)) ∧
    fullMate 22 k (deleted 22).1 = (deleted 22).1 ∧
    fullMate 22 k (deleted 22).2 = (deleted 22).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_23 (k : Choice) :
    (∀ i, fullMate 23 k (residualOrder 23 i) = residualOrder 23 (standardMate k i)) ∧
    fullMate 23 k (deleted 23).1 = (deleted 23).1 ∧
    fullMate 23 k (deleted 23).2 = (deleted 23).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_24 (k : Choice) :
    (∀ i, fullMate 24 k (residualOrder 24 i) = residualOrder 24 (standardMate k i)) ∧
    fullMate 24 k (deleted 24).1 = (deleted 24).1 ∧
    fullMate 24 k (deleted 24).2 = (deleted 24).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_25 (k : Choice) :
    (∀ i, fullMate 25 k (residualOrder 25 i) = residualOrder 25 (standardMate k i)) ∧
    fullMate 25 k (deleted 25).1 = (deleted 25).1 ∧
    fullMate 25 k (deleted 25).2 = (deleted 25).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_26 (k : Choice) :
    (∀ i, fullMate 26 k (residualOrder 26 i) = residualOrder 26 (standardMate k i)) ∧
    fullMate 26 k (deleted 26).1 = (deleted 26).1 ∧
    fullMate 26 k (deleted 26).2 = (deleted 26).2 := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fullMate_coordinates_27 (k : Choice) :
    (∀ i, fullMate 27 k (residualOrder 27 i) = residualOrder 27 (standardMate k i)) ∧
    fullMate 27 k (deleted 27).1 = (deleted 27).1 ∧
    fullMate 27 k (deleted 27).2 = (deleted 27).2 := by
  revert k
  decide +kernel

theorem fullMate_coordinates (d : PairIndex) (k : Choice) :
    (∀ i, fullMate d k (residualOrder d i) = residualOrder d (standardMate k i)) ∧
    fullMate d k (deleted d).1 = (deleted d).1 ∧
    fullMate d k (deleted d).2 = (deleted d).2 := by
  fin_cases d
  · exact fullMate_coordinates_0 k
  · exact fullMate_coordinates_1 k
  · exact fullMate_coordinates_2 k
  · exact fullMate_coordinates_3 k
  · exact fullMate_coordinates_4 k
  · exact fullMate_coordinates_5 k
  · exact fullMate_coordinates_6 k
  · exact fullMate_coordinates_7 k
  · exact fullMate_coordinates_8 k
  · exact fullMate_coordinates_9 k
  · exact fullMate_coordinates_10 k
  · exact fullMate_coordinates_11 k
  · exact fullMate_coordinates_12 k
  · exact fullMate_coordinates_13 k
  · exact fullMate_coordinates_14 k
  · exact fullMate_coordinates_15 k
  · exact fullMate_coordinates_16 k
  · exact fullMate_coordinates_17 k
  · exact fullMate_coordinates_18 k
  · exact fullMate_coordinates_19 k
  · exact fullMate_coordinates_20 k
  · exact fullMate_coordinates_21 k
  · exact fullMate_coordinates_22 k
  · exact fullMate_coordinates_23 k
  · exact fullMate_coordinates_24 k
  · exact fullMate_coordinates_25 k
  · exact fullMate_coordinates_26 k
  · exact fullMate_coordinates_27 k

/-- A perfect matching is its fixed-point-free involution on remaining ports. -/
structure Matching (d : PairIndex) where
  mate : Remaining d → Remaining d
  involutive : Function.Involutive mate
  no_fixed : ∀ v, mate v ≠ v

/-- No matching is omitted by the fifteen-candidate encoding. -/
theorem Matching.exists_choice {d : PairIndex} (M : Matching d) :
    ∃ k : Choice, ∀ i, (M.mate (residualEquiv d i)).val = fullMate d k (residualOrder d i) := by
  let e := residualEquiv d
  let m : Fin 6 → Fin 6 := fun i => e.symm (M.mate (e i))
  have hi : Function.Involutive m := by
    intro i
    simp only [m,e.apply_symm_apply]
    rw [M.involutive (e i),e.symm_apply_apply]
  have hn : ∀ i, m i ≠ i := by
    intro i hh
    apply M.no_fixed (e i)
    have h := congrArg e hh
    simpa only [m,e.apply_symm_apply] using h
  obtain ⟨k,hk⟩ := standardMate_complete m hi hn
  refine ⟨k,?_⟩
  intro i
  have h := congrArg e (congrFun hk i)
  have hv := congrArg Subtype.val h
  rw [(fullMate_coordinates d k).1 i]
  change (M.mate (e i)).val = (e (standardMate k i)).val
  simpa only [m,e.apply_symm_apply] using hv

end Paper2.Certificates.Q8.Atlas
