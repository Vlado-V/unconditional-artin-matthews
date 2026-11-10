module

public import ArtinMatthews.SpectralPeterssonHilbert
public import ArtinMatthews.SpectralPeterssonCuspForm
public import ArtinMatthews.SpectralPeterssonSourceGram
public import ArtinMatthews.SpectralPeterssonQCoefficient
public import ArtinMatthews.SpectralPeterssonSourceForms
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

/-! The normalized signed source vectors in the literal Petersson L²
space, with their actual inner products and diagonal norms. -/

noncomputable section
open MeasureTheory Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold InnerProductSpace ComplexConjugate Topology

namespace ArtinMatthews

abbrev Gamma0PeterssonL2 (N : ℕ) :=
  Lp ℂ 2 (volume.restrict (gamma0InteriorRegion N))

theorem gamma0PeterssonSignedCuspForm_memLp (N k : ℕ) [NeZero N] (negative : Bool)
    (F : CuspForm (gamma0PeterssonRealGroup N) (k : ℤ)) :
    MemLp (spectralPeterssonHilbertProfile k (spectralPeterssonSignVector negative F)) 2
      (volume.restrict (gamma0InteriorRegion N)) := by
  obtain ⟨M,hM⟩ := gamma0PeterssonCuspForm_weighted_bound N k F
  refine gamma0PeterssonHilbertProfile_memLp N k _ ?_ M ?_
  · cases negative
    · exact F.holo'.continuous
    · exact Complex.continuous_conj.comp F.holo'.continuous
  · intro z
    cases negative
    · exact hM z
    · change ‖conj (F z)‖*z.im^((k : ℝ)/2) ≤ M
      rw [Complex.norm_conj]
      exact hM z

theorem gamma0PeterssonSourceInfinity_memLp (N k : ℕ) [NeZero N] (hk : 2 ≤ k) (hEven : Even k)
    (negative : Bool) (n : ℕ+) :
    MemLp (spectralPeterssonHilbertProfile k
      (spectralPeterssonSignVector negative (gamma0PeterssonSourceInfinity N k n))) 2
      (volume.restrict (gamma0InteriorRegion N)) := by
  rw [← gamma0PeterssonSourceInfinityForm_coe N k hk hEven n]
  exact gamma0PeterssonSignedCuspForm_memLp N k negative (gamma0PeterssonSourceInfinityForm N k hk hEven n)

theorem gamma0PeterssonSourceAtkin_memLp (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (k : ℕ) (hk : 2 ≤ k) (hEven : Even k)
    (negative : Bool) (n : ℕ+) :
    MemLp (spectralPeterssonHilbertProfile k
      (spectralPeterssonSignVector negative (gamma0PeterssonSourceAtkin r s hab k n))) 2
      (volume.restrict (gamma0InteriorRegion (r*s))) := by
  rw [← gamma0PeterssonSourceAtkinForm_coe r s hcop hab k hk hEven n]
  exact gamma0PeterssonSignedCuspForm_memLp (r*s) k negative
    (gamma0PeterssonSourceAtkinForm r s hcop hab k hk hEven n)

def gamma0PeterssonSourceInfinityL2 (N k : ℕ) [NeZero N] (hk : 2 ≤ k) (hEven : Even k)
    (negative : Bool) (n : ℕ+) : Gamma0PeterssonL2 N :=
  (gamma0PeterssonSourceInfinity_memLp N k hk hEven negative n).toLp _

def gamma0PeterssonSourceAtkinL2 (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (k : ℕ) (hk : 2 ≤ k) (hEven : Even k)
    (negative : Bool) (n : ℕ+) : Gamma0PeterssonL2 (r*s) :=
  (gamma0PeterssonSourceAtkin_memLp r s hcop hab k hk hEven negative n).toLp _

theorem gamma0PeterssonSourceInfinityL2_coe (N k : ℕ) [NeZero N] (hk : 2 ≤ k) (hEven : Even k)
    (negative : Bool) (n : ℕ+) :
    ⇑(gamma0PeterssonSourceInfinityL2 N k hk hEven negative n)
      =ᵐ[volume.restrict (gamma0InteriorRegion N)]
      spectralPeterssonHilbertProfile k (spectralPeterssonSignVector negative (gamma0PeterssonSourceInfinity N k n)) :=
  (gamma0PeterssonSourceInfinity_memLp N k hk hEven negative n).coeFn_toLp

theorem gamma0PeterssonSourceAtkinL2_coe (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (k : ℕ) (hk : 2 ≤ k) (hEven : Even k)
    (negative : Bool) (n : ℕ+) :
    ⇑(gamma0PeterssonSourceAtkinL2 r s hcop hab k hk hEven negative n)
      =ᵐ[volume.restrict (gamma0InteriorRegion (r*s))]
      spectralPeterssonHilbertProfile k (spectralPeterssonSignVector negative (gamma0PeterssonSourceAtkin r s hab k n)) :=
  (gamma0PeterssonSourceAtkin_memLp r s hcop hab k hk hEven negative n).coeFn_toLp

theorem gamma0PeterssonSourceL2_mixed_inner (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (k : ℕ) (hk : 2 ≤ k) (hEven : Even k)
    (negative : Bool) (m n : ℕ+) :
    ⟪gamma0PeterssonSourceAtkinL2 r s hcop hab k hk hEven negative n,
      gamma0PeterssonSourceInfinityL2 (r*s) k hk hEven negative m⟫_ℂ =
      gamma0PeterssonInner (r*s) k
        (spectralPeterssonSignVector negative (gamma0PeterssonSourceAtkin r s hab k n))
        (spectralPeterssonSignVector negative (gamma0PeterssonSourceInfinity (r*s) k m)) :=
  gamma0PeterssonInner_eq_hilbert (r*s) k _ _
    (gamma0PeterssonSourceAtkin_memLp r s hcop hab k hk hEven negative n)
    (gamma0PeterssonSourceInfinity_memLp (r*s) k hk hEven negative m)

theorem gamma0PeterssonSourceInfinityL2_norm_sq (N k : ℕ) [NeZero N] (hk : 2 ≤ k) (hEven : Even k)
    (negative : Bool) (n : ℕ+) :
    ‖gamma0PeterssonSourceInfinityL2 N k hk hEven negative n‖^2 =
      1+(∑' c, gamma0PeterssonSignedGramModulusTerm N 1 1 k negative n n c).re := by
  unfold gamma0PeterssonSourceInfinityL2
  rw [gamma0PeterssonHilbert_diagonal_norm]
  simpa only [ite_eq_left rfl,ite_eq_left True.intro,Complex.add_re,Complex.one_re] using
    congrArg Complex.re (gamma0PeterssonSourceInfinity_signed_gram N k hk hEven negative n n).2

theorem gamma0PeterssonSourceAtkinL2_norm_sq (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (k : ℕ) (hk : 2 ≤ k) (hEven : Even k)
    (negative : Bool) (n : ℕ+) :
    ‖gamma0PeterssonSourceAtkinL2 r s hcop hab k hk hEven negative n‖^2 =
      1+(∑' c, gamma0PeterssonSignedGramModulusTerm (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s)
        k negative n n c).re := by
  unfold gamma0PeterssonSourceAtkinL2
  rw [gamma0PeterssonHilbert_diagonal_norm]
  simpa only [ite_eq_left rfl,ite_eq_left True.intro,Complex.add_re,Complex.one_re] using
    congrArg Complex.re (gamma0PeterssonSourceAtkin_signed_gram r s hcop hab k hk hEven negative n n).2

end ArtinMatthews
