module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import OAI.RepresentationTheory.Weil.Local.OscillatorProjection
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
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
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanCover
public import OAI.RepresentationTheory.Weil.Local.PolynomialMatrixAvoidance


set_option backward.privateInPublic true
@[expose] public section

/-! # Fourier Big Cell -/

namespace OAI.RepresentationTheory.Weil.Local.FourierBigCell.Construction

noncomputable section

/-! The symplectic domain with invertible Fourier block meets every finite collection of left translates. -/

open _root_.Matrix

variable {k : Type} [Field k] {n : ℕ}

def fourierBigCell (k : Type) [Field k] (n : ℕ) : Set (FunctionsMetaplectic.Construction.Symplectic k n) :=
  {g | g.val.toBlocks₁₂.det ≠ 0}

theorem weylSymplectic_inv_matrix :
    ((Generators.Construction.weylSymplectic k n)⁻¹).val = Matrix.fromBlocks 0 (-1) 1 0 := by
  rw [SymplecticGroup.coe_inv]
  simp [Generators.Construction.weylSymplectic, Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_neg]

theorem symplectic_exists_fourier_block_shift (g : FunctionsMetaplectic.Construction.Symplectic k n) :
    ∃ X : Matrix (Fin n) (Fin n) k, X.IsSymm ∧
      (g.val.toBlocks₁₂ + X * g.val.toBlocks₂₂).det ≠ 0 := by
  obtain ⟨X, hX⟩ := GenerationSymplectic.Construction.symplectic_exists_upper_bigCell (g * (Generators.Construction.weylSymplectic k n)⁻¹)
  refine ⟨X.val, X.property, ?_⟩
  change IsUnit (((GenerationSymplectic.Construction.upperSymplectic X).val * (g.val * ((Generators.Construction.weylSymplectic k n)⁻¹).val)).toBlocks₁₁).det at hX
  rw [weylSymplectic_inv_matrix, ← Matrix.fromBlocks_toBlocks g.val] at hX
  simpa [GenerationSymplectic.Construction.upperSymplectic, Matrix.fromBlocks_multiply] using hX.ne_zero

theorem fourierBigCell_finite_left_translates [Infinite k] (F : Finset (FunctionsMetaplectic.Construction.Symplectic k n)) :
    ∃ x : FunctionsMetaplectic.Construction.Symplectic k n, ∀ g ∈ F, x * g ∈ fourierBigCell k n := by
  obtain ⟨X, hX, hall⟩ := PolynomialMatrixAvoidance.Construction.exists_symmetric_all_determinants_ne_zero F
    (fun g => g.val.toBlocks₁₂) (fun g => g.val.toBlocks₂₂)
    (fun g _ => symplectic_exists_fourier_block_shift g)
  refine ⟨GenerationSymplectic.Construction.upperSymplectic ⟨X, hX⟩, ?_⟩
  intro g hg
  change (((GenerationSymplectic.Construction.upperSymplectic ⟨X, hX⟩).val * g.val).toBlocks₁₂).det ≠ 0
  rw [← Matrix.fromBlocks_toBlocks g.val]
  simpa [GenerationSymplectic.Construction.upperSymplectic, Matrix.fromBlocks_multiply] using hall g hg

theorem oscillator_fourierBigCell_finite_left_translates
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hnd : ¬ DiscreteTopology k) (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1) (hc : Continuous (fun t => ψ t))
    (hn : ∃ t : k, ψ t ≠ 1) (F : Finset (FunctionsMetaplectic.Construction.Oscillator k n ψ)) :
    ∃ x : FunctionsMetaplectic.Construction.Oscillator k n ψ, ∀ g ∈ F,
      OscillatorProjection.Construction.oscillatorProjection k n ψ (x * g) ∈ fourierBigCell k n := by
  classical
  obtain ⟨x, hx⟩ := fourierBigCell_finite_left_translates (F.image (OscillatorProjection.Construction.oscillatorProjection k n ψ))
  obtain ⟨a, ha⟩ := NonarchimedeanCover.Construction.nonarchimedean_metaplecticProjection_surjective hnd n ψ hu hc hn x
  refine ⟨a.val, ?_⟩
  intro g hg
  rw [map_mul]
  change FunctionsMetaplectic.Construction.metaplecticProjection k n ψ a * OscillatorProjection.Construction.oscillatorProjection k n ψ g ∈ fourierBigCell k n
  rw [ha]
  exact hx _ (Finset.mem_image_of_mem _ hg)

end

end OAI.RepresentationTheory.Weil.Local.FourierBigCell.Construction
