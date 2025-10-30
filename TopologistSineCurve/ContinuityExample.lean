import Mathlib.Topology.Basic

def Continuous' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ∀ V : Set Y, IsOpen V → IsOpen (f ⁻¹' V)
