module

public import ClassFieldTheory.AlgebraicNumberTheory.SUnit.LogLattice
public import Mathlib.Tactic.Module


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed compact logarithmic parallelepiped for reduction by actual
sixth powers of S-units. The complete lattice is the genuine all-place
S-unit logarithmic image, including the finite places in S. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SUnitGroup
open scoped NumberField Classical Pointwise
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def sUnitLogBasis (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  (Module.Free.chooseBasis ℤ (fullLogLattice (K := K) S)).ofZLatticeBasis ℝ

def sixthLogCompactSet (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Set (LogHyperplane (K := K) S) :=
  (fun z : LogHyperplane (K := K) S => (6 : ℝ) • z) ''
    (sUnitLogBasis K S).parallelepiped

theorem sixthLogCompactSet_isCompact (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsCompact (sixthLogCompactSet K S) :=
  (sUnitLogBasis K S).parallelepiped.isCompact.image (continuous_id.const_smul (6 : ℝ))

theorem exists_sUnit_sixth_log_reduction (S : Finset (HeightOneSpectrum (𝓞 K)))
    (z : LogHyperplane (K := K) S) :
    ∃ u : SUnitGroup (K := K) S,
      z + fullLog (K := K) S (Additive.ofMul (u ^ 6)) ∈ sixthLogCompactSet K S := by
  let b := sUnitLogBasis K S
  let x := (6 : ℝ)⁻¹ • z
  let f := ZSpan.floor b x
  have hf : (f : LogHyperplane (K := K) S) ∈ fullLogLattice (K := K) S := by
    have hb : Submodule.span ℤ (Set.range b) = fullLogLattice (K := K) S :=
      (Module.Free.chooseBasis ℤ (fullLogLattice (K := K) S)).ofZLatticeBasis_span ℝ
    exact hb.le f.property
  have hf' : (f : LogHyperplane (K := K) S) ∈
      LinearMap.range (fullLog (K := K) S).toIntLinearMap :=
    (fullLogLattice_eq_range (K := K) S).le hf
  obtain ⟨u, hu⟩ := hf'
  change fullLog (K := K) S u = (f : LogHyperplane (K := K) S) at hu
  refine ⟨u.toMul⁻¹, ?_⟩
  have hlog : fullLog (K := K) S (Additive.ofMul ((u.toMul⁻¹) ^ 6)) =
      -(6 : ℝ) • (f : LogHyperplane (K := K) S) := by
    change fullLog (K := K) S ((6 : ℕ) • (-u)) = _
    rw [map_nsmul, map_neg]
    change (6 : ℕ) • (-(fullLog (K := K) S u)) = _
    rw [hu]
    module
  rw [hlog]
  refine ⟨ZSpan.fract b x,
    ZSpan.fundamentalDomain_subset_parallelepiped b
      (ZSpan.fract_mem_fundamentalDomain b x), ?_⟩
  rw [ZSpan.fract_apply]
  change (6 : ℝ) • ((6 : ℝ)⁻¹ • z - (f : LogHyperplane (K := K) S)) = _
  module

end
end ArtinMatthews
