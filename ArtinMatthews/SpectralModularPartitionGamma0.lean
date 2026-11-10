module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import ArtinMatthews.SpectralModularPartition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan


set_option backward.privateInPublic true
@[expose] public section

/-! An actual open `Γ₀(N)` fundamental region, formed from the finitely many
inverse modular interior charts.  Its translates cover almost everywhere;
their only possible overlap is the central ineffective action of `±I`. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0InteriorChart (N : ℕ)
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : Set UpperHalfPlane :=
  (fun z : UpperHalfPlane => q.out • z) ⁻¹' ModularGroup.fdo

def gamma0InteriorRegion (N : ℕ) : Set UpperHalfPlane :=
  ⋃ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, gamma0InteriorChart N q

theorem gamma0InteriorChart_isOpen (N : ℕ)
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : IsOpen (gamma0InteriorChart N q) :=
  ModularGroup.isOpen_fdo.preimage
    (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ q.out))

theorem gamma0InteriorRegion_isOpen (N : ℕ) : IsOpen (gamma0InteriorRegion N) :=
  isOpen_iUnion (gamma0InteriorChart_isOpen N)

/-- The finitely many actual inverse modular interior charts are disjoint. -/
theorem gamma0InteriorChart_pairwiseDisjoint (N : ℕ) :
    Pairwise (fun q t => Disjoint (gamma0InteriorChart N q) (gamma0InteriorChart N t)) := by
  intro q t hqt
  rw [Set.disjoint_left]
  intro z hq ht
  change q.out • z ∈ ModularGroup.fdo at hq
  change t.out • z ∈ ModularGroup.fdo at ht
  have heq := gamma0_interior_overlap_quotient_eq N
    (γ := (1 : SL(2, ℤ))) (CongruenceSubgroup.Gamma0 N).one_mem hq
      (by simpa only [one_smul] using ht)
  exact hqt (by simpa only [Quotient.out_eq'] using heq)

/-- Every actual modular interior representative can be moved into the finite
`Γ₀(N)` region by an actual member of `Γ₀(N)`. -/
theorem gamma0InteriorRegion_of_modular_interior (N : ℕ)
    {z : UpperHalfPlane} {g : SL(2, ℤ)} (hg : g • z ∈ ModularGroup.fdo) :
    ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • z ∈ gamma0InteriorRegion N := by
  let q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N := g
  have hγ : q.out⁻¹ * g ∈ CongruenceSubgroup.Gamma0 N :=
    QuotientGroup.eq.mp (Quotient.out_eq' q)
  refine ⟨⟨q.out⁻¹ * g, hγ⟩, mem_iUnion.mpr ⟨q, ?_⟩⟩
  change q.out • ((q.out⁻¹ * g) • z) ∈ ModularGroup.fdo
  simpa only [mul_smul, smul_inv_smul] using hg

/-- The actual finite region covers the upper half-plane almost everywhere
under the congruence subgroup action. -/
theorem gamma0InteriorRegion_covers_ae (N : ℕ) :
    ∀ᵐ z : UpperHalfPlane ∂volume,
      ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • z ∈ gamma0InteriorRegion N := by
  filter_upwards [modular_exists_smul_mem_fdo_ae] with z hz
  obtain ⟨g, hg⟩ := hz
  exact gamma0InteriorRegion_of_modular_interior N hg

/-- An overlap of two `Γ₀(N)` translates of the actual open region forces the
central kernel `±I`, rather than falsely asserting a free `SL₂` action. -/
theorem gamma0InteriorRegion_overlap_central (N : ℕ)
    (γ : CongruenceSubgroup.Gamma0 N) {z : UpperHalfPlane}
    (hz : z ∈ gamma0InteriorRegion N)
    (hγz : (γ : SL(2, ℤ)) • z ∈ gamma0InteriorRegion N) :
    (γ : SL(2, ℤ)) = 1 ∨ (γ : SL(2, ℤ)) = -1 := by
  obtain ⟨q, hq⟩ := mem_iUnion.mp hz
  obtain ⟨t, ht⟩ := mem_iUnion.mp hγz
  have hqt : q = t := by
    have h := gamma0_interior_overlap_quotient_eq N γ.property hq ht
    simpa only [Quotient.out_eq'] using h
  subst t
  change q.out • z ∈ ModularGroup.fdo at hq
  change q.out • ((γ : SL(2, ℤ)) • z) ∈ ModularGroup.fdo at ht
  have hc : (q.out * (γ : SL(2, ℤ))) * q.out⁻¹ = 1 ∨
      (q.out * (γ : SL(2, ℤ))) * q.out⁻¹ = -1 :=
    ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo hq (by
      simpa only [mul_smul, inv_smul_smul] using ht)
  rcases hc with h | h
  · left
    have he := congrArg (fun u : SL(2, ℤ) => q.out⁻¹ * u * q.out) h
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
      inv_mul_cancel, one_mul, mul_one] using he
  · right
    have he := congrArg (fun u : SL(2, ℤ) => q.out⁻¹ * u * q.out) h
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
      mul_neg, neg_mul, inv_mul_cancel, one_mul, mul_one] using he

end ArtinMatthews
