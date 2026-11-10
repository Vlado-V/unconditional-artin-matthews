module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.GenerationSymplectic
public import OAI.RepresentationTheory.Weil.Local.Gaussian
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
public import OAI.RepresentationTheory.Weil.Local.FourierEquivalence
public import OAI.RepresentationTheory.Weil.Local.QuadraticIntertwiner


set_option backward.privateInPublic true
@[expose] public section

/-! # Oscillator Projection -/

namespace OAI.RepresentationTheory.Weil.Local.OscillatorProjection.Construction

noncomputable section

/-! The oscillator projection and normality of the intrinsic bare subgroup. -/

open scoped commutatorElement

variable (k : Type) [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ψ : AddChar k ℂ)

def oscillatorProjection : FunctionsMetaplectic.Construction.Oscillator k n ψ →* FunctionsMetaplectic.Construction.Symplectic k n :=
  (MonoidHom.fst _ _).comp (FunctionsMetaplectic.Construction.oscillatorSubgroup k n ψ).subtype

theorem oscillatorMinus_commute (g : FunctionsMetaplectic.Construction.Oscillator k n ψ) :
    Commute (FunctionsMetaplectic.Construction.oscillatorMinus k n ψ) g := by
  change FunctionsMetaplectic.Construction.oscillatorMinus k n ψ * g = g * FunctionsMetaplectic.Construction.oscillatorMinus k n ψ
  apply Subtype.ext
  apply Prod.ext
  · change 1 * g.val.1 = g.val.1 * 1
    simp
  · apply LinearEquiv.ext
    intro f
    change -(g.val.2 f) = g.val.2 (-f)
    exact (g.val.2.map_neg f).symm

theorem oscillatorMinus_conjugation (g : FunctionsMetaplectic.Construction.Oscillator k n ψ) :
    g * FunctionsMetaplectic.Construction.oscillatorMinus k n ψ * g⁻¹ = FunctionsMetaplectic.Construction.oscillatorMinus k n ψ := by
  rw [← (oscillatorMinus_commute k n ψ g).eq, mul_assoc, mul_inv_cancel, mul_one]

instance metaplecticSubgroup_normal : (FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ).Normal where
  conj_mem z hz g := by
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
        rcases hz with hz | hz
        · obtain ⟨u, v, rfl⟩ := hz
          apply Subgroup.subset_closure
          left
          exact ⟨g * u * g⁻¹, g * v * g⁻¹, (conjugate_commutatorElement u v g).symm⟩
        · obtain rfl := hz
          rw [oscillatorMinus_conjugation]
          exact Subgroup.subset_closure (Or.inr rfl)
    | one => simp
    | mul a b _ _ ha hb =>
        rw [← conj_mul]
        exact (FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ).mul_mem ha hb
    | inv a _ ha =>
        rw [← conj_inv]
        exact (FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ).inv_mem ha

omit [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] in
theorem upper_quadratic_conjugation (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) :
    GenerationSymplectic.Construction.upperSymplectic B = (Generators.Construction.weylSymplectic k n)⁻¹ *
      Generators.Construction.quadraticSymplectic ⟨-B.val, B.property.neg⟩ * Generators.Construction.weylSymplectic k n := by
  apply Subtype.ext
  change Matrix.fromBlocks 1 B.val 0 1 =
    ((Generators.Construction.weylSymplectic k n)⁻¹).val * (Generators.Construction.quadraticSymplectic ⟨-B.val, B.property.neg⟩).val *
      (Generators.Construction.weylSymplectic k n).val
  rw [SymplecticGroup.coe_inv]
  simp [Generators.Construction.weylSymplectic, Generators.Construction.quadraticSymplectic, Matrix.J, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

theorem real_oscillatorProjection_surjective_standard :
    Function.Surjective (oscillatorProjection ℝ n (Gaussian.Construction.realCharacter 1)) := by
  apply MonoidHom.range_eq_top.mp
  apply GenerationSymplectic.Construction.subgroup_eq_top_of_symplectic_generators
  · intro B
    refine ⟨(FourierEquivalence.Construction.realFourierOscillator n)⁻¹ *
      QuadraticIntertwiner.Construction.realQuadraticOscillator 1 ⟨-B.val, B.property.neg⟩ * FourierEquivalence.Construction.realFourierOscillator n, ?_⟩
    rw [map_mul, map_mul, map_inv]
    exact (upper_quadratic_conjugation ℝ n B).symm
  · intro A
    exact ⟨LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter 1) A, rfl⟩
  · exact ⟨FourierEquivalence.Construction.realFourierOscillator n, rfl⟩

end

end OAI.RepresentationTheory.Weil.Local.OscillatorProjection.Construction
