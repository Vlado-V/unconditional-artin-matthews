module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import OAI.RepresentationTheory.Weil.Local.OscillatorProjection
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanFourier
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanNorm
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanTestSpace


set_option backward.privateInPublic true
@[expose] public section

/-! # Nonarchimedean Cover -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanCover.Construction

noncomputable section

/-! Surjectivity of the actual bare metaplectic projection over ultrametric local fields. -/

open _root_.MeasureTheory

theorem exists_nonarchimedean_fourier_oscillator
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) :
    ∃ w : FunctionsMetaplectic.Construction.Oscillator k n ψ, OscillatorProjection.Construction.oscillatorProjection k n ψ w = Generators.Construction.weylSymplectic k n := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let μ : Measure (FunctionsMetaplectic.Construction.Position k n) := Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k))
  let : μ.IsAddHaarMeasure := by dsimp [μ]; infer_instance
  obtain ⟨a, T, _, hT, hunitary⟩ :=
    NonarchimedeanFourier.Construction.exists_nonarchimedean_unitary_fourier hNondiscrete n ψ hu hc hn μ
  exact ⟨⟨(Generators.Construction.weylSymplectic k n, T), ⟨hunitary,
    NonarchimedeanFourier.Construction.scalar_fourier_intertwines hNondiscrete ψ hu hc μ (a : ℂ) T hT⟩⟩, rfl⟩

theorem ultrametric_metaplecticProjection_surjective
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) :
    Function.Surjective (FunctionsMetaplectic.Construction.metaplecticProjection k n ψ) := by
  obtain ⟨w, hw⟩ := exists_nonarchimedean_fourier_oscillator hNondiscrete n ψ hu hc hn
  apply MonoidHom.range_eq_top.mp
  apply GenerationSymplectic.Construction.subgroup_eq_top_of_symplectic_unipotents
  · intro B
    let u := NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic hNondiscrete ψ hu hc ⟨-B.val, B.property.neg⟩
    have h : w⁻¹ * u.val * w ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ := by
      have hh := (inferInstance : (FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ).Normal).conj_mem
        u.val u.property w⁻¹
      simpa only [inv_inv] using hh
    refine ⟨⟨w⁻¹ * u.val * w, h⟩, ?_⟩
    change OscillatorProjection.Construction.oscillatorProjection k n ψ (w⁻¹ * u.val * w) = GenerationSymplectic.Construction.upperSymplectic B
    rw [map_mul, map_mul, map_inv, hw]
    exact (OscillatorProjection.Construction.upper_quadratic_conjugation k n B).symm
  · intro B
    exact ⟨NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic hNondiscrete ψ hu hc B, rfl⟩

theorem nonarchimedean_metaplecticProjection_surjective
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) :
    Function.Surjective (FunctionsMetaplectic.Construction.metaplecticProjection k n ψ) := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hNondiscrete
  exact ultrametric_metaplecticProjection_surjective hNondiscrete n ψ hu hc hn

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanCover.Construction
