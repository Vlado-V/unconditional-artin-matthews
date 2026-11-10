module

public import ArtinMatthews.GiantSignedEdgeRealPairing
public import ArtinMatthews.GiantSignedEdgeDegreeTonelli
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


set_option backward.privateInPublic true
@[expose] public section

/-! The full coupled edge test and its exact survivor-degree decomposition. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev GiantSignedEdgeCoupledTest {J : Type*} (P : J → Finset ℕ) (t : J → ℕ)
    (E : Type*) :=
  ((j : J) → Finset (Fin (t j))) → ((j : J) → Finset (Fin (t j))) →
    GiantSignedPrimeTuple P t → GiantSignedPrimeTuple P t →
      GiantSignedMemory P → GiantSignedMemory P → E

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
    [∀ j, ∀ p : P j, NeZero p.val] {t : J → ℕ}

def giantSignedEdgeJointRealWeight (ν : (j : J) → P j → ℝ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (S T : (j : J) → Finset (Fin (t j)))
    (source target : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P)
    (e : (j : J) → Fin (T j).card ↪ Fin (m.1 j)) : ℝ :=
  giantSignedFreePrimeRealMass ν source * giantSignedMemoryMass ν m *
    (∏ j, (V j)⁻¹ ^ (T j).card) * giantSignedFreshPrimeRealMass ν T target *
    giantSignedPendingDamping ρ m *
    giantSignedPendingDamping ρ (giantSignedEdgeTarget d m source ⟨S, T, e⟩)

def giantSignedEdgeCoupledTerm (ν : (j : J) → P j → ℝ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (F : GiantSignedEdgeCoupledTest P t ℝ)
    (S T : (j : J) → Finset (Fin (t j)))
    (source target : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P)
    (e : (j : J) → Fin (T j).card ↪ Fin (m.1 j)) : ℝ :=
  if GiantSignedEdgeHits d m target ⟨S, T, e⟩ then
    giantSignedEdgeJointRealWeight ν V ρ d S T source target m e *
      F S T source target m (giantSignedEdgeTarget d m source ⟨S, T, e⟩)
  else 0

def giantSignedEdgeCoupledENNTerm (ν : (j : J) → P j → ℝ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (F : GiantSignedEdgeCoupledTest P t ℝ≥0∞)
    (S T : (j : J) → Finset (Fin (t j)))
    (source target : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P)
    (e : (j : J) → Fin (T j).card ↪ Fin (m.1 j)) : ℝ≥0∞ :=
  if GiantSignedEdgeHits d m target ⟨S, T, e⟩ then
    ENNReal.ofReal (giantSignedEdgeJointRealWeight ν V ρ d S T source target m e) *
      F S T source target m (giantSignedEdgeTarget d m source ⟨S, T, e⟩)
  else 0

def giantSignedEdgeCoupledApply (ν : (j : J) → P j → ℝ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (F : GiantSignedEdgeCoupledTest P t ℝ)
    (source : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P) : ℝ :=
  ∑ S : (j : J) → Finset (Fin (t j)), ∑ T : (j : J) → Finset (Fin (t j)),
    ∑ target : GiantSignedPrimeTuple P t,
      (∏ j, (V j)⁻¹ ^ (T j).card) * giantSignedFreshPrimeRealMass ν T target *
        ∑ e : (j : J) → Fin (T j).card ↪ Fin (m.1 j),
          if GiantSignedEdgeHits d m target ⟨S, T, e⟩ then
            giantSignedPendingDamping ρ m *
              giantSignedPendingDamping ρ (giantSignedEdgeTarget d m source ⟨S, T, e⟩) *
                F S T source target m (giantSignedEdgeTarget d m source ⟨S, T, e⟩)
          else 0

def giantSignedEdgeCoupledPairing (ν : (j : J) → P j → ℝ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (F : GiantSignedEdgeCoupledTest P t ℝ) : ℝ :=
  ∑ source : GiantSignedPrimeTuple P t, giantSignedFreePrimeRealMass ν source *
    ∑' m : GiantSignedMemory P,
      giantSignedMemoryMass ν m * giantSignedEdgeCoupledApply ν V ρ d F source m

def giantSignedEdgeCoupledENNPairing (ν : (j : J) → P j → ℝ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (F : GiantSignedEdgeCoupledTest P t ℝ≥0∞) : ℝ≥0∞ :=
  ∑ source : GiantSignedPrimeTuple P t, ∑' m : GiantSignedMemory P,
    ∑ S : (j : J) → Finset (Fin (t j)), ∑ T : (j : J) → Finset (Fin (t j)),
      ∑ target : GiantSignedPrimeTuple P t, ∑ e,
        giantSignedEdgeCoupledENNTerm ν V ρ d F S T source target m e

def giantSignedEdgeENNStorePairing (ν : (j : J) → P j → ℝ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedEdgeCoupledTest P t ℝ≥0∞) : ℝ≥0∞ :=
  ∑ source : GiantSignedPrimeTuple P t, ∑ target : GiantSignedPrimeTuple P t,
    ∑ old : GiantSignedParticleTuple P (fun j => n j + (T j).card), ∑ e,
      giantSignedEdgeCoupledENNTerm ν V ρ d F S T source target
        ⟨fun j => n j + (T j).card, old⟩ e

omit [DecidableEq J] [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedFreePrimeRealMass_nonneg (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (source : GiantSignedPrimeTuple P t) :
    0 ≤ giantSignedFreePrimeRealMass ν source :=
  Finset.prod_nonneg fun j _ => Finset.prod_nonneg fun i _ => hν j (source j i)

omit [DecidableEq J] [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedEdgeJointRealWeight_nonneg (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℤ) (S T : (j : J) → Finset (Fin (t j)))
    (source target : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P)
    (e : (j : J) → Fin (T j).card ↪ Fin (m.1 j)) :
    0 ≤ giantSignedEdgeJointRealWeight ν V ρ d S T source target m e := by
  have ha := giantSignedFreePrimeRealMass_nonneg ν hν source
  have hb := giantSignedMemoryMass_nonneg ν hν m
  have hc : 0 ≤ ∏ j, (V j)⁻¹ ^ (T j).card :=
    Finset.prod_nonneg fun j _ => pow_nonneg (inv_nonneg.mpr (hV j)) _
  have hd := giantSignedFreshPrimeRealMass_nonneg ν hν T target
  have he := giantSignedPendingDamping_nonneg hρ m
  have hf := giantSignedPendingDamping_nonneg hρ
    (giantSignedEdgeTarget d m source ⟨S, T, e⟩)
  unfold giantSignedEdgeJointRealWeight
  positivity

omit [DecidableEq J] [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedEdgeCoupledTerm_nonneg (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℤ) (F : GiantSignedEdgeCoupledTest P t ℝ)
    (hF : ∀ S T source target old out, 0 ≤ F S T source target old out)
    (S T : (j : J) → Finset (Fin (t j)))
    (source target : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P)
    (e : (j : J) → Fin (T j).card ↪ Fin (m.1 j)) :
    0 ≤ giantSignedEdgeCoupledTerm ν V ρ d F S T source target m e := by
  unfold giantSignedEdgeCoupledTerm
  split_ifs
  · exact mul_nonneg (giantSignedEdgeJointRealWeight_nonneg ν hν V hV hρ d S T source target m e)
      (hF _ _ _ _ _ _)
  · exact le_rfl

omit [DecidableEq J] [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedEdgeCoupledTerm_mono (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℤ) (F G : GiantSignedEdgeCoupledTest P t ℝ)
    (hFG : ∀ S T source target old out, F S T source target old out ≤ G S T source target old out)
    (S T : (j : J) → Finset (Fin (t j)))
    (source target : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P)
    (e : (j : J) → Fin (T j).card ↪ Fin (m.1 j)) :
    giantSignedEdgeCoupledTerm ν V ρ d F S T source target m e ≤
      giantSignedEdgeCoupledTerm ν V ρ d G S T source target m e := by
  unfold giantSignedEdgeCoupledTerm
  split_ifs
  · exact mul_le_mul_of_nonneg_left (hFG _ _ _ _ _ _)
      (giantSignedEdgeJointRealWeight_nonneg ν hν V hV hρ d S T source target m e)
  · exact le_rfl

omit [DecidableEq J] [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedEdgeCoupledENNTerm_ofReal (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℤ) (F : GiantSignedEdgeCoupledTest P t ℝ)
    (S T : (j : J) → Finset (Fin (t j)))
    (source target : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P)
    (e : (j : J) → Fin (T j).card ↪ Fin (m.1 j)) :
    giantSignedEdgeCoupledENNTerm ν V ρ d
        (fun S T source target old out => ENNReal.ofReal (F S T source target old out))
        S T source target m e =
      ENNReal.ofReal (giantSignedEdgeCoupledTerm ν V ρ d F S T source target m e) := by
  unfold giantSignedEdgeCoupledENNTerm giantSignedEdgeCoupledTerm
  split_ifs
  · exact (ENNReal.ofReal_mul
      (giantSignedEdgeJointRealWeight_nonneg ν hν V hV hρ d S T source target m e)).symm
  · simp only [ENNReal.ofReal_zero]

theorem giantSignedEdgeCoupledENNPairing_blocks
    (ν : (j : J) → P j → ℝ) (V : J → ℝ) (ρ : ℝ) (d : ℤ)
    (F : GiantSignedEdgeCoupledTest P t ℝ≥0∞) :
    giantSignedEdgeCoupledENNPairing ν V ρ d F =
      ∑ S : (j : J) → Finset (Fin (t j)), ∑ T : (j : J) → Finset (Fin (t j)),
        ∑' n : J → ℕ, giantSignedEdgeENNStorePairing ν V ρ d n S T F := by
  unfold giantSignedEdgeCoupledENNPairing giantSignedEdgeENNStorePairing
  calc
    _ = ∑ S : (j : J) → Finset (Fin (t j)), ∑ T : (j : J) → Finset (Fin (t j)),
        ∑ source : GiantSignedPrimeTuple P t, ∑ target : GiantSignedPrimeTuple P t,
          ∑' m : GiantSignedMemory P, ∑ e,
            giantSignedEdgeCoupledENNTerm ν V ρ d F S T source target m e := by
      simpa only [tsum_fintype] using ennreal_tsum_five_reorder
        (fun (source : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P)
          (S T : (j : J) → Finset (Fin (t j))) (target : GiantSignedPrimeTuple P t) =>
            ∑ e, giantSignedEdgeCoupledENNTerm ν V ρ d F S T source target m e)
    _ = ∑ S : (j : J) → Finset (Fin (t j)), ∑ T : (j : J) → Finset (Fin (t j)),
        ∑ source : GiantSignedPrimeTuple P t, ∑ target : GiantSignedPrimeTuple P t,
          ∑' n : J → ℕ,
            ∑ old : GiantSignedParticleTuple P (fun j => n j + (T j).card), ∑ e,
              giantSignedEdgeCoupledENNTerm ν V ρ d F S T source target
                ⟨fun j => n j + (T j).card, old⟩ e := by
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro T _
      apply Finset.sum_congr rfl
      intro source _
      apply Finset.sum_congr rfl
      intro target _
      exact giantSignedEdgeMemory_tsum_shift T
        (fun m e => giantSignedEdgeCoupledENNTerm ν V ρ d F S T source target m e)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro T _
      simpa only [tsum_fintype] using ennreal_tsum_three_rotate
        (fun (source target : GiantSignedPrimeTuple P t) (n : J → ℕ) =>
          ∑ old : GiantSignedParticleTuple P (fun j => n j + (T j).card), ∑ e,
            giantSignedEdgeCoupledENNTerm ν V ρ d F S T source target
              ⟨fun j => n j + (T j).card, old⟩ e)

theorem giantSignedEdgeRealStorePairing_eq_terms
    (ν : (j : J) → P j → ℝ) (V : J → ℝ) (ρ : ℝ) (d : ℤ)
    (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedEdgeCoupledTest P t ℝ) :
    giantSignedEdgeRealStorePairing ν V ρ d n S T (F S T) =
      ∑ source : GiantSignedPrimeTuple P t, ∑ target : GiantSignedPrimeTuple P t,
        ∑ old : GiantSignedParticleTuple P (fun j => n j + (T j).card), ∑ e,
          giantSignedEdgeCoupledTerm ν V ρ d F S T source target
            ⟨fun j => n j + (T j).card, old⟩ e := by
  unfold giantSignedEdgeRealStorePairing giantSignedEdgeCoupledTerm
    giantSignedEdgeJointRealWeight
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro target _
  apply Finset.sum_congr rfl
  intro old _
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> ring

theorem giantSignedEdgeRealStorePairing_nonneg
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 ≤ V j) {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℤ)
    (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedEdgeCoupledTest P t ℝ)
    (hF : ∀ S T source target old out, 0 ≤ F S T source target old out) :
    0 ≤ giantSignedEdgeRealStorePairing ν V ρ d n S T (F S T) := by
  rw [giantSignedEdgeRealStorePairing_eq_terms]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      giantSignedEdgeCoupledTerm_nonneg ν hν V hV hρ d F hF _ _ _ _ _ _

theorem giantSignedEdgeRealStorePairing_mono
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 ≤ V j) {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℤ)
    (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j)))
    (F G : GiantSignedEdgeCoupledTest P t ℝ)
    (hFG : ∀ S T source target old out, F S T source target old out ≤ G S T source target old out) :
    giantSignedEdgeRealStorePairing ν V ρ d n S T (F S T) ≤
      giantSignedEdgeRealStorePairing ν V ρ d n S T (G S T) := by
  rw [giantSignedEdgeRealStorePairing_eq_terms, giantSignedEdgeRealStorePairing_eq_terms]
  apply Finset.sum_le_sum
  intro source _
  apply Finset.sum_le_sum
  intro target _
  apply Finset.sum_le_sum
  intro old _
  apply Finset.sum_le_sum
  intro e _
  exact giantSignedEdgeCoupledTerm_mono ν hν V hV hρ d F G hFG _ _ _ _ _ _

end
end ArtinMatthews
