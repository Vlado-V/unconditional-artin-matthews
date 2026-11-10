module

public import ArtinMatthews.SourceQuadraticSieveEnergy
public import ArtinMatthews.SourceReflectionExpansion
public import OAI.NumberTheory.DirichletL.QuadraticSieve.FiniteOperator
public import ArtinMatthews.SourceQuadraticSwappedSieve
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
public import OAI.NumberTheory.DirichletL.CubicSieve.Operator
public import OAI.NumberTheory.DirichletL.QuadraticSieve.CoprimeBilinearBound


set_option backward.privateInPublic true
@[expose] public section

/-! The original Small term is controlled on its complete row ball. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain StandardAdelic OAI.FiniteSieveOperator
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

def sourceQuadraticSmallCoprimePair (cols : Finset E) (a : E) (u v : E → ℂ) : ℂ :=
  ∑ b ∈ cols, ∑ c ∈ cols, if Disjoint b.support c.support then
    star (u b) * v c * χ a b * χ a c else 0

def sourceQuadraticSmallWeightedMass (cols : Finset E) (u : E → ℂ) : ℝ :=
  ∑ b ∈ cols, (2 : ℝ) ^ b.support.card * ‖u b‖ ^ 2

theorem sourceQuadraticSmallCoprimePair_cauchy (rows cols : Finset E) (u v : E → ℂ) :
    (∑ a ∈ rows, ‖sourceQuadraticSmallCoprimePair F S₀ hζ cols a u v‖) ^ 2 ≤
      (‖operator (fun (a : rows) (b : cols) => χ a.val b.val)‖ ^ 2 *
        sourceQuadraticSmallWeightedMass F S₀ cols u) *
      (‖operator (fun (a : rows) (b : cols) => χ a.val b.val)‖ ^ 2 *
        sourceQuadraticSmallWeightedMass F S₀ cols v) := by
  let B := cols.biUnion (fun b => b.support)
  let A : Matrix rows cols ℂ := fun a b => χ a.val b.val
  have hsupport (b : cols) : b.val.support ⊆ B := by
    intro P hP
    exact Finset.mem_biUnion.mpr ⟨b.val, b.property, hP⟩
  have hbound := OAI.CoprimeBilinearSieve.coprime_bilinear_operator_bound
    B (fun b : cols => b.val.support) (fun b : cols => b.val.support) hsupport hsupport
    (fun a b => star (A a b)) A (fun b => u b.val) (fun b => v b.val)
  have hconj : ‖operator (fun a b => star (A a b))‖ = ‖operator A‖ :=
    OAI.SevenEighths.CubicSieve.operator_conjugate_norm A
  rw [hconj] at hbound
  have hinner (a : rows) :
      (∑ b : cols, ∑ c : cols, if Disjoint b.val.support c.val.support then
        star (star (A a b) * u b.val) * (A a c * v c.val) else 0) =
        sourceQuadraticSmallCoprimePair F S₀ hζ cols a.val u v := by
    unfold sourceQuadraticSmallCoprimePair
    rw [← Finset.sum_coe_sort cols (fun b => ∑ c ∈ cols,
      if Disjoint b.support c.support then star (u b) * v c * χ a.val b * χ a.val c else 0)]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.sum_coe_sort cols (fun c =>
      if Disjoint b.val.support c.support then star (u b.val) * v c * χ a.val b.val * χ a.val c else 0)]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hd : Disjoint b.val.support c.val.support
    · simp only [ite_eq_left hd, star_mul, star_star, A]
      ring
    · simp only [ite_eq_right hd]
  simp_rw [hinner] at hbound
  have hrow : (∑ a : rows, ‖sourceQuadraticSmallCoprimePair F S₀ hζ cols a.val u v‖) =
      ∑ a ∈ rows, ‖sourceQuadraticSmallCoprimePair F S₀ hζ cols a u v‖ :=
    Finset.sum_coe_sort rows (fun a : E => ‖sourceQuadraticSmallCoprimePair F S₀ hζ cols a u v‖)
  rw [hrow] at hbound
  have hmu : (∑ b : cols, (2 : ℝ) ^ b.val.support.card * ‖u b.val‖ ^ 2) =
      sourceQuadraticSmallWeightedMass F S₀ cols u := by
    change _ = ∑ b ∈ cols, (2 : ℝ) ^ b.support.card * ‖u b‖ ^ 2
    exact Finset.sum_coe_sort cols (fun b : E => (2 : ℝ) ^ b.support.card * ‖u b‖ ^ 2)
  have hmv : (∑ b : cols, (2 : ℝ) ^ b.val.support.card * ‖v b.val‖ ^ 2) =
      sourceQuadraticSmallWeightedMass F S₀ cols v := by
    change _ = ∑ b ∈ cols, (2 : ℝ) ^ b.support.card * ‖v b‖ ^ 2
    exact Finset.sum_coe_sort cols (fun b : E => (2 : ℝ) ^ b.support.card * ‖v b‖ ^ 2)
  rw [hmu, hmv] at hbound
  exact hbound

variable [IsTotallyComplex F]

theorem sourceQuadraticSmallCoprimePair_ball_bound {α : ℝ}
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ K P : ℝ, 1 ≤ K → 1 ≤ P → ∀ rows cols : Finset E,
      (∀ a ∈ rows, sourceReflectionIsSquarefree a ∧ (q a : ℝ) ≤ K) →
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ (q b : ℝ) ≤ 2 * P) →
      ∀ u v : E → ℂ,
      ∑ a ∈ rows, ‖sourceQuadraticSmallCoprimePair F S₀ hζ cols a u v‖ ≤
        C * (K * P) ^ η * (P + K ^ α) *
          Real.sqrt (sourceQuadraticSmallWeightedMass F S₀ cols u) *
          Real.sqrt (sourceQuadraticSmallWeightedMass F S₀ cols v) := by
  obtain ⟨C, hC, hnorm⟩ := sourceQuadratic_swapped_norm_bound F S₀ hζ htrace hE η hη
  refine ⟨C, hC, ?_⟩
  intro K P hK hP rows cols hrows hcols u v
  let B := C * (K * P) ^ η * (P + K ^ α)
  let A := operator (fun (a : rows) (b : cols) => χ a.val b.val)
  let mu := sourceQuadraticSmallWeightedMass F S₀ cols u
  let mv := sourceQuadraticSmallWeightedMass F S₀ cols v
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmu : 0 ≤ mu := Finset.sum_nonneg (fun _ _ => by positivity)
  have hmv : 0 ≤ mv := Finset.sum_nonneg (fun _ _ => by positivity)
  have hA : ‖A‖ ^ 2 ≤ B := hnorm K P (by linarith) (by linarith) rows cols
    (fun a ha => ⟨(hrows a ha).1, (hrows a ha).2.trans (by linarith)⟩) hcols
  have hc := sourceQuadraticSmallCoprimePair_cauchy F S₀ hζ rows cols u v
  change (∑ a ∈ rows, ‖sourceQuadraticSmallCoprimePair F S₀ hζ cols a u v‖) ^ 2 ≤
    (‖A‖ ^ 2 * mu) * (‖A‖ ^ 2 * mv) at hc
  have hs : (∑ a ∈ rows, ‖sourceQuadraticSmallCoprimePair F S₀ hζ cols a u v‖) ^ 2 ≤
      (B * Real.sqrt mu * Real.sqrt mv) ^ 2 := by
    apply hc.trans
    calc
      _ ≤ (B * mu) * (B * mv) := by gcongr
      _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hmu, Real.sq_sqrt hmv]; ring
  exact (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)).mp hs

end
end ArtinMatthews.SourceEulerAssembly
