module

public import ArtinMatthews.VaryingKummerAnalyticHeckeIdealMobius
public import ArtinMatthews.QuadraticHeckeSquarefreeSplit
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

namespace ArtinMatthews
open NumberField VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
open HeckeIdealMobius (divisors)

/-- The finite set of squarefree integral ideals satisfying the actual real cutoff. -/
def quadraticHeckeSquarefreeCutoff (H : ℝ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) (Nat.ceil H)).toFinset.filter
    (fun a => Squarefree a ∧ (Ideal.absNorm a : ℝ) ≤ H)

theorem mem_quadraticHeckeSquarefreeCutoff {H : ℝ} {a : Ideal (𝓞 K)} :
    a ∈ quadraticHeckeSquarefreeCutoff K H ↔
      Squarefree a ∧ (Ideal.absNorm a : ℝ) ≤ H := by
  simp only [quadraticHeckeSquarefreeCutoff, Finset.mem_filter,
    Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · exact And.right
  · intro ha
    refine ⟨?_, ha⟩
    exact_mod_cast ha.2.trans (Nat.le_ceil H)

/-- The same finite cutoff with a fixed coprimality condition. -/
def quadraticHeckeCoprimeCutoff (g : Ideal (𝓞 K)) (H : ℝ) : Finset (Ideal (𝓞 K)) :=
  (quadraticHeckeSquarefreeCutoff K H).filter (fun a => IsCoprime a g)

theorem mem_quadraticHeckeCoprimeCutoff {g a : Ideal (𝓞 K)} {H : ℝ} :
    a ∈ quadraticHeckeCoprimeCutoff K g H ↔
      Squarefree a ∧ (Ideal.absNorm a : ℝ) ≤ H ∧ IsCoprime a g := by
  simp only [quadraticHeckeCoprimeCutoff, Finset.mem_filter,
    mem_quadraticHeckeSquarefreeCutoff]
  tauto

theorem quadraticHeckeNorm_le_norm_mul_right (a : Ideal (𝓞 K))
    {d : Ideal (𝓞 K)} (hd : d ≠ ⊥) :
    (Ideal.absNorm a : ℝ) ≤ Ideal.absNorm (a * d) := by
  have hp : 0 < Ideal.absNorm d :=
    Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hd)
  have hn : Ideal.absNorm a ≤ Ideal.absNorm a * Ideal.absNorm d :=
    Nat.le_mul_of_pos_right _ hp
  exact_mod_cast (show Ideal.absNorm a ≤ Ideal.absNorm (a * d) by simpa only [map_mul] using hn)

/-- Reindex the literal squarefree cutoff by its coprime part and its divisor of `g`.
The transformed cutoff remains on the product, including at nonintegral values of `H`. -/
theorem quadraticHeckeSquarefreeCutoff_split (g : Ideal (𝓞 K)) (hg : Squarefree g)
    (H : ℝ) (f : Ideal (𝓞 K) → ℂ) :
    (∑ a ∈ quadraticHeckeSquarefreeCutoff K H, f a) =
      ∑ h ∈ quadraticHeckeCoprimeCutoff K g H, ∑ d ∈ divisors K g,
        if (Ideal.absNorm (h * d) : ℝ) ≤ H then f (h * d) else 0 := by
  let T := ((quadraticHeckeCoprimeCutoff K g H) ×ˢ (divisors K g)).filter
    (fun p => (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ H)
  have hT (p : Ideal (𝓞 K) × Ideal (𝓞 K)) : p ∈ T ↔
      (Squarefree p.1 ∧ (Ideal.absNorm p.1 : ℝ) ≤ H ∧ IsCoprime p.1 g) ∧
        p.2 ∣ g ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ H := by
    simp only [T, Finset.mem_filter, Finset.mem_product,
      mem_quadraticHeckeCoprimeCutoff, HeckeIdealMobius.mem_divisors K hg.ne_zero]
    tauto
  have hsum : (∑ p ∈ T, f (p.1 * p.2)) =
      ∑ a ∈ quadraticHeckeSquarefreeCutoff K H, f a := by
    apply Finset.sum_bij (fun p _ => p.1 * p.2)
    · intro p hp
      obtain ⟨hh, hd, hn⟩ := (hT p).1 hp
      apply (mem_quadraticHeckeSquarefreeCutoff K).2
      refine ⟨?_, hn⟩
      exact (quadraticHeckeSquarefreeCoprimeSplit K g hg
        (⟨p.1, hh.1, hh.2.2⟩, ⟨p.2, hd⟩)).property
    · intro p hp q hq hpq
      obtain ⟨hh, hd, _⟩ := (hT p).1 hp
      obtain ⟨hqh, hqd, _⟩ := (hT q).1 hq
      have he := (quadraticHeckeSquarefreeCoprimeSplit K g hg).injective
        (show quadraticHeckeSquarefreeCoprimeSplit K g hg
            (⟨p.1, hh.1, hh.2.2⟩, ⟨p.2, hd⟩) =
          quadraticHeckeSquarefreeCoprimeSplit K g hg
            (⟨q.1, hqh.1, hqh.2.2⟩, ⟨q.2, hqd⟩) from Subtype.ext hpq)
      exact Prod.ext (congrArg (fun r => r.1.val) he) (congrArg (fun r => r.2.val) he)
    · intro a ha
      obtain ⟨hs, hn⟩ := (mem_quadraticHeckeSquarefreeCutoff K).1 ha
      obtain ⟨p, hp⟩ := (quadraticHeckeSquarefreeCoprimeSplit K g hg).surjective ⟨a, hs⟩
      have hv : p.1.val * p.2.val = a := congrArg Subtype.val hp
      refine ⟨(p.1.val, p.2.val), (hT _).2 ?_, hv⟩
      refine ⟨⟨p.1.property.1, ?_, p.1.property.2⟩, p.2.property, hv ▸ hn⟩
      have hd : p.2.val ≠ ⊥ := ne_zero_of_dvd_ne_zero hg.ne_zero p.2.property
      exact (quadraticHeckeNorm_le_norm_mul_right K p.1.val hd).trans (hv ▸ hn)
    · intro p _
      rfl
  rw [← hsum, Finset.sum_filter, Finset.sum_product]

end
end ArtinMatthews
