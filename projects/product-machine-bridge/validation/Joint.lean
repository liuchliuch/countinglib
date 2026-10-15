import Counting.Algorithm.ProductFinitePalette.Clients
import Counting.Algorithm.Affine.FixedLanguage

/-! Joint old/new consumer import check. The old public Product evaluator is
already imported through the new frontend. No provider relocation is needed. -/

#check Counting.Algorithm.Product.run_eq_partition
#check Counting.Algorithm.Affine.FixedLanguage.computes
#check Counting.Algorithm.ProductFinitePalette.computes
#check Counting.Algorithm.ProductFinitePalette.Clients.repeated_machine_run
