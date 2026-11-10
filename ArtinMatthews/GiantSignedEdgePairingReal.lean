module

public import ArtinMatthews.GiantSignedEdgeCoupledPairing
public import ArtinMatthews.GiantSignedEdgePairingConvergence
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Finite real Fubini for the original coupled, optionally banned edge row. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem ennreal_ofReal_sum_four
    {A : Type*} {B : A → Type*} {C : (a : A) → B a → Type*}
    {D : (a : A) → (b : B a) → C a b → Type*}
    [Fintype A] [∀ a, Fintype (B a)] [∀ a b, Fintype (C a b)]
    [∀ a b c, Fintype (D a b c)]
    (f : (a : A) → (b : B a) → (c : C a b) → D a b c → ℝ)
    (hf : ∀ a b c d, 0 ≤ f a b c d) :
    ENNReal.ofReal (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, ENNReal.ofReal (f a b c d) := by
  have h := ENNReal.ofReal_sum_of_nonneg
    (s := Finset.univ)
    (f := fun z : (Σ a, Σ b : B a, Σ c : C a b, D a b c) =>
      f z.1 z.2.1 z.2.2.1 z.2.2.2)
    (fun z _ => hf z.1 z.2.1 z.2.2.1 z.2.2.2)
  simpa only [Fintype.sum_sigma] using h

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
    [∀ j, ∀ p : P j, NeZero p.val] {t : J → ℕ}

theorem giantSignedEdgeENNStorePairing_ofReal
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 ≤ V j) {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℤ)
    (F : GiantSignedEdgeCoupledTest P t ℝ)
    (hF : ∀ S T source target old out, 0 ≤ F S T source target old out)
    (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j))) :
    giantSignedEdgeENNStorePairing ν V ρ d n S T
        (fun S T source target old out => ENNReal.ofReal (F S T source target old out)) =
      ENNReal.ofReal (giantSignedEdgeRealStorePairing ν V ρ d n S T (F S T)) := by
  unfold giantSignedEdgeENNStorePairing
  simp_rw [giantSignedEdgeCoupledENNTerm_ofReal ν hν V hV hρ]
  rw [giantSignedEdgeRealStorePairing_eq_terms]
  exact (ennreal_ofReal_sum_four
    (fun source target old e => giantSignedEdgeCoupledTerm ν V ρ d F S T source target
      ⟨fun j => n j + (T j).card, old⟩ e)
    (fun _ _ _ _ => giantSignedEdgeCoupledTerm_nonneg ν hν V hV hρ d F hF _ _ _ _ _ _)).symm

omit [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedEdgeCoupledENNRow_ofReal
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 ≤ V j) {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℤ)
    (F : GiantSignedEdgeCoupledTest P t ℝ)
    (hF : ∀ S T source target old out, 0 ≤ F S T source target old out)
    (source : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P) :
    (∑ S : (j : J) → Finset (Fin (t j)), ∑ T : (j : J) → Finset (Fin (t j)),
      ∑ target : GiantSignedPrimeTuple P t, ∑ e,
        giantSignedEdgeCoupledENNTerm ν V ρ d
          (fun S T source target old out => ENNReal.ofReal (F S T source target old out))
          S T source target m e) =
      ENNReal.ofReal (giantSignedFreePrimeRealMass ν source *
        (giantSignedMemoryMass ν m * giantSignedEdgeCoupledApply ν V ρ d F source m)) := by
  simp_rw [giantSignedEdgeCoupledENNTerm_ofReal ν hν V hV hρ]
  rw [giantSignedEdgeCoupled_weighted_eq_terms]
  exact (ennreal_ofReal_sum_four
    (fun S T target e => giantSignedEdgeCoupledTerm ν V ρ d F S T source target m e)
    (fun _ _ _ _ => giantSignedEdgeCoupledTerm_nonneg ν hν V hV hρ d F hF _ _ _ _ _ _)).symm

theorem giantSignedEdgeCoupledENNPairing_ne_top
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 < V j) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (d : ℤ)
    (F : GiantSignedEdgeCoupledTest P t ℝ)
    (hF0 : ∀ S T source target old out, 0 ≤ F S T source target old out)
    (B u v : ℝ) (hB : 0 ≤ B) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hF : ∀ S T source target old out,
      F S T source target old out ≤ B * u ^ (∑ j, old.1 j) * v ^ (∑ j, out.1 j)) :
    giantSignedEdgeCoupledENNPairing ν V ρ d
      (fun S T source target old out => ENNReal.ofReal (F S T source target old out)) ≠ ∞ := by
  unfold giantSignedEdgeCoupledENNPairing
  simp_rw [giantSignedEdgeCoupledENNRow_ofReal ν hν V (fun j => (hV j).le) hρ d F hF0]
  apply ENNReal.sum_ne_top.mpr
  intro source _
  exact ((giantSignedEdgeCoupled_memory_summable ν hν V hV hρ hρ1 d F hF0
    B u v hB hu hv hF source).mul_left (giantSignedFreePrimeRealMass ν source)).tsum_ofReal_ne_top

theorem giantSignedEdgeRealStorePairing_summable
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 < V j) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (d : ℤ)
    (F : GiantSignedEdgeCoupledTest P t ℝ)
    (hF0 : ∀ S T source target old out, 0 ≤ F S T source target old out)
    (B u v : ℝ) (hB : 0 ≤ B) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hF : ∀ S T source target old out,
      F S T source target old out ≤ B * u ^ (∑ j, old.1 j) * v ^ (∑ j, out.1 j))
    (S T : (j : J) → Finset (Fin (t j))) :
    Summable (fun n : J → ℕ => giantSignedEdgeRealStorePairing ν V ρ d n S T (F S T)) := by
  have htotal := giantSignedEdgeCoupledENNPairing_ne_top ν hν V hV hρ hρ1 d F hF0 B u v hB hu hv hF
  rw [giantSignedEdgeCoupledENNPairing_blocks] at htotal
  simp_rw [giantSignedEdgeENNStorePairing_ofReal ν hν V (fun j => (hV j).le) hρ d F hF0] at htotal
  have hST : (∑' n : J → ℕ,
      ENNReal.ofReal (giantSignedEdgeRealStorePairing ν V ρ d n S T (F S T))) ≠ ∞ := by
    apply ne_top_of_le_ne_top htotal
    let R := fun (S T : (j : J) → Finset (Fin (t j))) =>
      ∑' n : J → ℕ, ENNReal.ofReal (giantSignedEdgeRealStorePairing ν V ρ d n S T (F S T))
    have hT : R S T ≤ ∑ U, R S U :=
      Finset.single_le_sum (f := fun U => R S U) (fun _ _ => bot_le) (Finset.mem_univ T)
    have hS : (∑ U, R S U) ≤ ∑ V, ∑ U, R V U :=
      Finset.single_le_sum (f := fun V => ∑ U, R V U) (fun _ _ => bot_le) (Finset.mem_univ S)
    exact hT.trans hS
  exact (ENNReal.summable_toReal hST).congr (fun n => ENNReal.toReal_ofReal
    (giantSignedEdgeRealStorePairing_nonneg ν hν V (fun j => (hV j).le) hρ d n S T F hF0))

theorem giantSignedEdgeCoupledENNPairing_toReal
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 < V j) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (d : ℤ)
    (F : GiantSignedEdgeCoupledTest P t ℝ)
    (hF0 : ∀ S T source target old out, 0 ≤ F S T source target old out)
    (B u v : ℝ) (hB : 0 ≤ B) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hF : ∀ S T source target old out,
      F S T source target old out ≤ B * u ^ (∑ j, old.1 j) * v ^ (∑ j, out.1 j)) :
    (giantSignedEdgeCoupledENNPairing ν V ρ d
      (fun S T source target old out => ENNReal.ofReal (F S T source target old out))).toReal =
        giantSignedEdgeCoupledPairing ν V ρ d F := by
  have hs (source : GiantSignedPrimeTuple P t) :=
    (giantSignedEdgeCoupled_memory_summable ν hν V hV hρ hρ1 d F hF0
      B u v hB hu hv hF source).mul_left (giantSignedFreePrimeRealMass ν source)
  unfold giantSignedEdgeCoupledENNPairing giantSignedEdgeCoupledPairing
  simp_rw [giantSignedEdgeCoupledENNRow_ofReal ν hν V (fun j => (hV j).le) hρ d F hF0]
  rw [ENNReal.toReal_sum (fun source _ => (hs source).tsum_ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro source _
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  calc
    _ = ∑' m : GiantSignedMemory P, giantSignedFreePrimeRealMass ν source *
        (giantSignedMemoryMass ν m * giantSignedEdgeCoupledApply ν V ρ d F source m) := by
      apply tsum_congr
      intro m
      exact ENNReal.toReal_ofReal (mul_nonneg (giantSignedFreePrimeRealMass_nonneg ν hν source)
        (mul_nonneg (giantSignedMemoryMass_nonneg ν hν m)
          (giantSignedEdgeCoupledApply_nonneg ν hν V (fun j => (hV j).le) hρ d F hF0 source m)))
    _ = _ := tsum_mul_left

theorem giantSignedEdgeCoupledPairing_blocks
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 < V j) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (d : ℤ)
    (F : GiantSignedEdgeCoupledTest P t ℝ)
    (hF0 : ∀ S T source target old out, 0 ≤ F S T source target old out)
    (B u v : ℝ) (hB : 0 ≤ B) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hF : ∀ S T source target old out,
      F S T source target old out ≤ B * u ^ (∑ j, old.1 j) * v ^ (∑ j, out.1 j)) :
    giantSignedEdgeCoupledPairing ν V ρ d F =
      ∑ S : (j : J) → Finset (Fin (t j)), ∑ T : (j : J) → Finset (Fin (t j)),
        ∑' n : J → ℕ, giantSignedEdgeRealStorePairing ν V ρ d n S T (F S T) := by
  have hs (S T : (j : J) → Finset (Fin (t j))) :=
    giantSignedEdgeRealStorePairing_summable ν hν V hV hρ hρ1 d F hF0 B u v hB hu hv hF S T
  rw [← giantSignedEdgeCoupledENNPairing_toReal ν hν V hV hρ hρ1 d F hF0 B u v hB hu hv hF,
    giantSignedEdgeCoupledENNPairing_blocks]
  simp_rw [giantSignedEdgeENNStorePairing_ofReal ν hν V (fun j => (hV j).le) hρ d F hF0]
  rw [ENNReal.toReal_sum (fun S _ => ENNReal.sum_ne_top.mpr
    (fun T _ => (hs S T).tsum_ofReal_ne_top))]
  apply Finset.sum_congr rfl
  intro S _
  rw [ENNReal.toReal_sum (fun T _ => (hs S T).tsum_ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro T _
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro n
  exact ENNReal.toReal_ofReal
    (giantSignedEdgeRealStorePairing_nonneg ν hν V (fun j => (hV j).le) hρ d n S T F hF0)

omit [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedEdgeApply_eq_coe_coupled
    (ν : (j : J) → P j → ℝ) (V : J → ℝ) (ρ : ℝ) (d : ℤ) (D : ℕ)
    (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ) (m : GiantSignedMemory P) :
    giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
        (fun target out => (f target out : ℂ)) m =
      (giantSignedEdgeCoupledApply ν V ρ d
        (fun _ T _ target _ out =>
          if GiantSignedEdgePromotionBan D T target then f target out else 0) source m : ℂ) := by
  unfold giantSignedEdgeApply giantSignedEdgeCoupledApply giantSignedPromotionCharge
    giantSignedFreshPrimeMass giantSignedFreshPrimeRealMass
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod,
    Complex.ofReal_pow, Complex.ofReal_inv]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro target _
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases hh : GiantSignedEdgeHits d m target ⟨S, T, e⟩
  · by_cases hb : GiantSignedEdgePromotionBan D T target
    · simp [hh, hb]
    · simp [hh, hb]
  · simp [hh]

omit [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedEdgeApply_re_eq_coupled
    (ν : (j : J) → P j → ℝ) (V : J → ℝ) (ρ : ℝ) (d : ℤ) (D : ℕ)
    (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ) (m : GiantSignedMemory P) :
    (giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
      (fun target out => (f target out : ℂ)) m).re =
      giantSignedEdgeCoupledApply ν V ρ d
        (fun _ T _ target _ out =>
          if GiantSignedEdgePromotionBan D T target then f target out else 0) source m := by
  rw [giantSignedEdgeApply_eq_coe_coupled]
  rfl

end
end ArtinMatthews
