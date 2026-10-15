import Counting.Reduction.FixedGadget.All
import Holant.Complexity.FixedGadgetSubstitution.Adjoin
import Holant.Complexity.FixedGadgetSubstitution.OriginalFamily

set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
set_option pp.proofs false

-- Canonical providers; these names are retained, not copied into the public package.
#check Holant.Complexity.FixedGadgetSubstitution.Template
#check Holant.Complexity.FixedGadgetSubstitution.Template.WellFormed
#check Holant.Complexity.FixedGadgetSubstitution.Template.network
#check Holant.Complexity.FixedGadgetSubstitution.replace
#check Holant.Complexity.FixedGadgetSubstitution.replace_wellFormed
#check Holant.Complexity.FixedGadgetSubstitution.replacement_partition
#check Holant.Complexity.FixedGadgetSubstitution.Compiler.templateComputes
#check Holant.Complexity.FixedGadgetSubstitution.Compiler.expandRows_vertices_indexed
#check Holant.Complexity.FixedGadgetSubstitution.Compiler.indexed_edges
#check Holant.Complexity.FixedGadgetSubstitution.Compiler.rawComputes
#check Holant.Complexity.FixedGadgetSubstitution.Compiler.value
#check Holant.Complexity.FixedGadgetSubstitution.Compiler.computes
#check Holant.Complexity.FixedGadgetSubstitution.Compiler.inFP
#check Holant.Complexity.FixedGadgetSubstitution.Compiler.primitive_bound
#check Holant.Complexity.FixedGadgetSubstitution.replace_length_le
#check Holant.Complexity.FixedGadgetSubstitution.templateCoordinates
#check Holant.Complexity.FixedGadgetSubstitution.templateFamilyReduction
#check Holant.Complexity.FixedGadgetSubstitution.reduction
#check Holant.Complexity.FixedGadgetSubstitution.Adjoin.old_coordinates
#check Holant.Complexity.FixedGadgetSubstitution.Adjoin.new_coordinates
#check Holant.Complexity.FixedGadgetSubstitution.Adjoin.reduction
#check Holant.Complexity.FixedGadgetSubstitution.OriginalFamily.ambientSource_family
#check Holant.Complexity.FixedGadgetSubstitution.OriginalFamily.source_value_exact
#check Holant.Complexity.FixedGadgetSubstitution.OriginalFamily.reduction

-- New public statements.
#check Counting.Reduction.FixedGadget.compile
#check Counting.Reduction.FixedGadget.value_compile
#check Counting.Reduction.FixedGadget.computes
#check Counting.Reduction.FixedGadget.output_length
#check Counting.Reduction.FixedGadget.output_length_static
#check Counting.Reduction.FixedGadget.primitive_bound
#check Counting.Reduction.FixedGadget.parsimonious
#check Counting.Reduction.FixedGadget.inFP_of_base
#check Counting.Reduction.FixedGadget.hard_base_of_extension
#check Counting.Reduction.FixedGadget.extension_inFP_iff
#check Counting.Reduction.FixedGadget.extension_equivalent
#check Counting.Reduction.FixedGadget.exactReduction
#check Counting.Reduction.FixedGadget.exactReduction_time
#check Counting.Reduction.FixedGadget.exactHardnessTransport
#check Counting.Reduction.FixedGadget.templatePresentation_table
#check Counting.Reduction.FixedGadget.partition_compile_network
#check Counting.Reduction.FixedGadget.substitution_alignment

#check Counting.Reduction.FixedGadget.extension_hard_iff
