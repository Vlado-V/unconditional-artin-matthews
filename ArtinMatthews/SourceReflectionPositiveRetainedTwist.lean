module

public import ArtinMatthews.SourceReflectionPositiveFiniteTwist
public import ArtinMatthews.SourceKPRetainedSeedExterior
public import ArtinMatthews.SourceKPCuspResidualFourierUpper
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


set_option backward.privateInPublic true
@[expose] public section

/-! The positive translations sit to the right of the retained diagonal
and before the original seed translates. They commute across the
retained diagonal because their places are exterior. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic Matrix QuadraticWeil
open scoped NumberField Classical BigOperators AdeleRing MatrixGroups

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "S" => sourceHilbertSet K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Nf" => sourceKPFiniteAdeleUpperLift K hζ
local notation "B" => sourceKPRetainedFiniteBase K hζ
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "U" => sourceReflectionPositiveTwistAdele K hζ S₀
local notation "wt" => sourceReflectionPositiveTwistWeight K hζ S₀
local notation "Seed" => sourceKPRetainedSeedFourierAt K hζ S

attribute [local instance] positiveTwistLabelFintype

theorem sourceReflectionExteriorUpperAdele_commute
    (F : Finset (SourceExteriorPrime K S₀)) (x : (P : F) → P.val.val.adicCompletion K)
    (qf : Gf) (hqf : ∀ P : F, B P.val.val qf = 1) :
    Commute (Nf (sourceKPExteriorUpperAdele K S₀ F x)) qf := by
  unfold sourceKPExteriorUpperAdele
  have h (T : Finset ↥F) :
      Commute (Nf (∑ P ∈ T, sourceKPFiniteAdditiveSingle K P.val.val (x P))) qf := by
    induction T using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, sourceKPFiniteAdeleUpperLift_zero]
      exact Commute.one_left _
    | @insert P T hP ih =>
      let p := P.val.val
      let g := sourceFiniteKP2ProjectiveLift K hζ p (sourceGL2Upper (x P))
      let q : SourceKPAdelicProjective K hζ := (1,qf)
      have hbase : sourceKPAdelicLocalBase K hζ p q = 1 := hqf P
      have hl := congrArg Prod.snd (sourceKPAdelicLocalProjective_upper K hζ p (x P))
      change (sourceKPAdelicLocalProjective K hζ p g).2 =
        Nf (sourceKPFiniteAdditiveSingle K p (x P)) at hl
      have hloc : Commute (Nf (sourceKPFiniteAdditiveSingle K p (x P))) qf := by
        rw [← hl]
        exact congrArg Prod.snd
          (sourceKPAdelicLocalProjective_commute_of_base_one K hζ p g q hbase).eq
      rw [Finset.sum_insert hP, sourceKPFiniteAdeleUpperLift_add]
      exact hloc.mul_left ih
  exact h Finset.univ

theorem sourceReflectionPositiveTwistAdele_commute_retained
    (e : E) (u : SourceReflectionPositiveTwistLabels K S₀ e)
    (z : ∀ P : S, (P.val.adicCompletion K)ˣ) :
    Commute (Nf (U e u)) (D (sourceKPRetainedDiagonalUnit K S z)) :=
  sourceReflectionExteriorUpperAdele_commute K hζ S₀ e.support
    (fun P => sourceReflectionPositiveLocalTranslation K hζ S₀ P.val (u P)) _
    (fun P => sourceKPRetainedFiniteBase_diagonalUnit_notMem K hζ S z P.val.val P.val.property)

theorem sourceReflectionRetainedSeedFourierAt_left_finite_upper
    (R M : S → ℕ) (m : Kˣ) {T : ℝ} (hT : 1 ≤ T) (q₀ qf : Gf) (u : 𝔸ᶠ[K]) :
    Seed R M hT m q₀ (Nf u*qf) =
      finiteCharacter K (algebraMap K 𝔸ᶠ[K] (m:K)*u)*Seed R M hT m q₀ qf := by
  unfold sourceKPRetainedSeedFourierAt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, sourceKPCuspResidualFourierValue_left_finite_upper]
  ring

def sourceReflectionPositiveRetainedTwist
    (e : E) (R M : S → ℕ) (m : Kˣ) {T : ℝ} (hT : 1 ≤ T) (q₀ : Gf)
    (z : ∀ P : S, (P.val.adicCompletion K)ˣ) : ℂ :=
  ∑ u : SourceReflectionPositiveTwistLabels K S₀ e, wt e u *
    Seed R M hT m q₀ (D (sourceKPRetainedDiagonalUnit K S z) * Nf (U e u))

theorem sourceReflectionPositiveRetainedTwist_eq
    (hS : standardWeilBadPlaces K ⊆ S) (e : E) (R M : S → ℕ) (m : Kˣ)
    (x : sourceRing K S₀) (hx : (m:K) = (x:K))
    {T : ℝ} (hT : 1 ≤ T) (q₀ : Gf) (z : ∀ P : S, (P.val.adicCompletion K)ˣ) :
    sourceReflectionPositiveRetainedTwist K hζ S₀ e R M m hT q₀ z =
      reflectionExponentResidueValue K hζ S₀ e x *
        Seed R M hT m q₀ (D (sourceKPRetainedDiagonalUnit K S z)) := by
  let d := D (sourceKPRetainedDiagonalUnit K S z)
  let W := Seed R M hT m q₀
  have he : sourceReflectionPositiveRetainedTwist K hζ S₀ e R M m hT q₀ z =
      sourceReflectionPositiveFiniteTwist K hζ S₀ e W d := by
    unfold sourceReflectionPositiveRetainedTwist sourceReflectionPositiveFiniteTwist
    apply Finset.sum_congr rfl
    intro u _
    change wt e u * W (d*Nf (U e u)) = wt e u * W (Nf (U e u)*d)
    rw [(sourceReflectionPositiveTwistAdele_commute_retained K hζ S₀ e u z).eq]
  rw [he, sourceReflectionPositiveFiniteTwist_eq_residueValue K hζ S₀ hS e m x hx]
  exact sourceReflectionRetainedSeedFourierAt_left_finite_upper K hζ S₀ R M m hT q₀ d

theorem sourceReflectionPositiveRetainedTwist_monomial
    (hS : standardWeilBadPlaces K ⊆ S) (e a : E) (R M : S → ℕ)
    {T : ℝ} (hT : 1 ≤ T) (q₀ : Gf) (z : ∀ P : S, (P.val.adicCompletion K)ˣ) :
    sourceReflectionPositiveRetainedTwist K hζ S₀ e R M (sourcePrimeExponentUnit K hζ S₀ a) hT q₀ z =
      reflectionExponentResidueValue K hζ S₀ e (sourcePrimeExponentGenerator K hζ S₀ a) *
        Seed R M hT (sourcePrimeExponentUnit K hζ S₀ a) q₀ (D (sourceKPRetainedDiagonalUnit K S z)) :=
  sourceReflectionPositiveRetainedTwist_eq K hζ S₀ hS e R M _
    (sourcePrimeExponentGenerator K hζ S₀ a) (sourcePrimeExponentUnit_val K hζ S₀ a) hT q₀ z

theorem sourceReflectionPositiveRetainedUnitTwist_eq
    (hS : standardWeilBadPlaces K ⊆ S) (e : E) (R M : S → ℕ) (m : Kˣ)
    (x : sourceRing K S₀) (hx : (m:K) = (x:K))
    {T : ℝ} (hT : 1 ≤ T) (q₀ : Gf) (z : ∀ P : S, (P.val.adicCompletion K)ˣ) :
    let d := D (sourceKPRetainedDiagonalUnit K S z)
    (∑ u : SourceReflectionPositiveTwistLabels K S₀ e, wt e u *
      Seed R M hT 1 q₀ (sourceKPCuspResidualUnitTranslate K hζ m (d*Nf (U e u)))) =
      reflectionExponentResidueValue K hζ S₀ e x *
        Seed R M hT 1 q₀ (sourceKPCuspResidualUnitTranslate K hζ m d) := by
  intro d
  let b := sourceKPCuspResidualFrequencyScale K hζ m (1/6)
  let W := Seed R M hT m q₀
  have h (u : SourceReflectionPositiveTwistLabels K S₀ e) :
      wt e u * Seed R M hT 1 q₀ (sourceKPCuspResidualUnitTranslate K hζ m (d*Nf (U e u))) =
      b*(wt e u * W (d*Nf (U e u))) := by
    rw [sourceKPRetainedSeedFourierAt_unit_translate]
    change wt e u * (b * W (d * Nf (U e u))) = _
    exact mul_left_comm _ _ _
  simp_rw [h]
  rw [← Finset.mul_sum]
  change b * sourceReflectionPositiveRetainedTwist K hζ S₀ e R M m hT q₀ z = _
  rw [sourceReflectionPositiveRetainedTwist_eq K hζ S₀ hS e R M m x hx,
    sourceKPRetainedSeedFourierAt_unit_translate]
  change b * (reflectionExponentResidueValue K hζ S₀ e x * W d) =
    reflectionExponentResidueValue K hζ S₀ e x * (b * W d)
  exact mul_left_comm _ _ _

end
end ArtinMatthews
