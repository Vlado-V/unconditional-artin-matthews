module

public import ArtinMatthews.ShiftedABLRhoModulusSupport
public import ArtinMatthews.SpectralABLMixedScalarReindex
public import ArtinMatthews.ShiftedABLMellinCircle
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The separated signed source term is the full arithmetic side of
the actual mixed-cusp trace, with its signed frequencies intact. -/

noncomputable section
open Set OAI OAI.Erdos970.ErdosKloosterman
open scoped BigOperators
namespace ArtinMatthews

theorem shiftedABLMellinKloosterman_eq_mixed_standard (F m3 m4 : ℕ) (c : ℕ)
    (hr : (m3*m4).Coprime F) (hc : 0 < c ∧ (m3*m4).Coprime c) (hF : 0 < F) (ρ : ℤ) :
    let r := m3*m4
    let n := (m3 : ℤ)-(m4 : ℤ)
    let hrq : r.Coprime (F*c) := Nat.coprime_mul_iff_right.mpr ⟨hr,hc.2⟩
    let _ : NeZero (F*c) := ⟨(Nat.mul_pos hF hc.1).ne'⟩
    shiftedABLMellinKloosterman (F*c) m3 m4 ρ =
      standardSum (F*c) (ρ*spectral_inverseUnitRepresentative r (F*c) hrq) n := by
  let r := m3*m4
  let q := F*c
  let hrq : r.Coprime q := Nat.coprime_mul_iff_right.mpr ⟨hr,hc.2⟩
  have hq : q ≠ 0 := (Nat.mul_pos hF hc.1).ne'
  let _ : NeZero q := ⟨hq⟩
  change shiftedABLMellinKloosterman q m3 m4 ρ =
    standardSum q (ρ*spectral_inverseUnitRepresentative r q hrq) ((m3 : ℤ)-(m4 : ℤ))
  rw [shiftedABLMellinKloosterman,dif_neg hq,shiftedABLThetaRhoKloosterman,standardSum,
    sum_swap,Int.cast_sub,Int.cast_natCast,Int.cast_natCast,Int.cast_mul,
    spectral_inverseUnitRepresentative_cast,← ZMod.inv_coe_unit,ZMod.coe_unitOfCoprime]
  push_cast
  rw [mul_comm]
  simp only [r,Nat.cast_mul]

theorem shiftedABLRhoOrbitalArgument_signed (F m3 m4 : ℕ) (ρ : ℤ) (c : ℝ) :
    shiftedABLRhoOrbitalArgument F (shiftedABLFirstIndex m3 m4) (m3*m4) ρ c =
      4*Real.pi*Real.sqrt (|(ρ : ℝ)*(((m3 : ℤ)-(m4 : ℤ) : ℤ) : ℝ)|)/
        ((F : ℝ)*Real.sqrt ((m3*m4 : ℕ) : ℝ)*c) := by
  unfold shiftedABLRhoOrbitalArgument shiftedABLMellinJNumerator shiftedABLFirstIndex
  simp only [abs_mul,← Int.cast_abs,← Nat.cast_natAbs]

theorem shiftedABLRhoCommonModulusSum_eq_tsum
    (F L m3 m4 : ℕ) [NeZero F] (hr : (m3*m4).Coprime F)
    (hL : 0 < L) (hm3 : 0 < m3) (hm4 : 0 < m4) (hne : m3 ≠ m4)
    {R : ℝ} (hR : 0 < R) {ρ : ℤ} (hρ : (ρ.natAbs : ℝ) ≤ 2*R) (u : ℝ) :
    let r := m3*m4
    let n := (m3 : ℤ)-(m4 : ℤ)
    let a := shiftedABLRhoBlockScale L (shiftedABLFirstIndex m3 m4) r R
    let f (C : ℝ) := shiftedABLRhoCommonTest a u (4*Real.pi*Real.sqrt (|(ρ : ℝ)*(n : ℝ)|)/C)
    (∑ c ∈ shiftedABLCommonModuli r L,
      shiftedABLMellinKloosterman (F*c) m3 m4 ρ/(c : ℂ)*
        shiftedABLRhoCommonTest a u (shiftedABLRhoOrbitalArgument F (shiftedABLFirstIndex m3 m4) r ρ c)) =
      ∑' c, gamma0MixedSourceModulusTerm r F hr ρ n f c := by
  classical
  let r := m3*m4
  let n := (m3 : ℤ)-(m4 : ℤ)
  let a := shiftedABLRhoBlockScale L (shiftedABLFirstIndex m3 m4) r R
  let f (C : ℝ) := shiftedABLRhoCommonTest a u (4*Real.pi*Real.sqrt (|(ρ : ℝ)*(n : ℝ)|)/C)
  let S := shiftedABLCommonModuli r L
  let T := gamma0MixedSourceModulusTerm r F hr ρ n f
  have hF : 0 < F := NeZero.pos F
  have hr₀ : 0 < r := Nat.mul_pos hm3 hm4
  have hn : 0 < shiftedABLFirstIndex m3 m4 :=
    Int.natAbs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
  let E : {c // c ∈ S} ↪ {c : ℕ // 0 < c ∧ r.Coprime c} :=
    ⟨fun c => ⟨c.val,(Finset.mem_Icc.mp (Finset.mem_filter.mp c.property).1).1,
      (Finset.mem_filter.mp c.property).2.symm⟩,
      fun x y h => Subtype.ext (congrArg (fun c : {c : ℕ // 0 < c ∧ r.Coprime c} => c.val) h)⟩
  let U := S.attach.map E
  have hz (c : {c : ℕ // 0 < c ∧ r.Coprime c}) (hc : c ∉ U) : T c = 0 := by
    have hbig : 18*L < c.val := by
      by_contra h
      have hmem : c.val ∈ S :=
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨c.property.1,le_of_not_gt h⟩,c.property.2.symm⟩
      exact hc (Finset.mem_map.mpr ⟨⟨c.val,hmem⟩,Finset.mem_attach _ _,Subtype.ext rfl⟩)
    have h := shiftedABLRhoCommonTest_zero_of_modulus_large hF hL hn hr₀ hR hρ hbig u
    rw [shiftedABLRhoOrbitalArgument_signed] at h
    change _ * f ((F : ℝ)*Real.sqrt (r : ℝ)*(c.val : ℝ)) = 0
    rw [show f ((F : ℝ)*Real.sqrt (r : ℝ)*(c.val : ℝ)) = 0 from h,mul_zero]
  change _ = ∑' c, T c
  rw [tsum_eq_sum hz,show U = S.attach.map E from rfl,Finset.sum_map]
  rw [← Finset.sum_attach S]
  apply Finset.sum_congr rfl
  intro c _
  have h₁ := (E c).property
  unfold T gamma0MixedSourceModulusTerm
  dsimp only
  rw [shiftedABLMellinKloosterman_eq_mixed_standard F m3 m4 c.val hr h₁ hF ρ,
    shiftedABLRhoOrbitalArgument_signed]
  let _ : NeZero (F*c.val) := ⟨(Nat.mul_pos hF h₁.1).ne'⟩
  let K := standardSum (F*c.val)
    (ρ*spectral_inverseUnitRepresentative r (F*c.val)
      (Nat.coprime_mul_iff_right.mpr ⟨hr,h₁.2⟩)) n
  let V := f ((F : ℝ)*Real.sqrt (r : ℝ)*(c.val : ℝ))
  change K/(c.val : ℂ)*V = (1/(c.val : ℂ))*K*V
  ring

end ArtinMatthews
