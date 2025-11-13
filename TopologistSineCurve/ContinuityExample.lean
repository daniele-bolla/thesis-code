import Mathlib

open Topology Filter Set
variable {X Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable (f : X → Y) (x : X)

theorem Continuous'''.tendsto (hf : Continuous f) (x) :
  Tendsto f (𝓝 x) (𝓝 (f x)) := by
  rw [(nhds_basis_opens x).tendsto_iff (nhds_basis_opens (f x))]
  intro t ⟨hft_in, ht_open⟩
  use f ⁻¹' t
  constructor
  · exact ⟨hft_in, ht_open.preimage hf⟩
  · exact Subset.rfl
