module

public import ArtinMatthews.SpectralPeterssonSourceForms
public import ArtinMatthews.SpectralPeterssonHilbert
public import ArtinMatthews.SpectralPeterssonQCoefficient
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

/-! Actual finite packets of the normalized Poincare cusp forms. -/
noncomputable section
open Set Matrix MeasureTheory UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold BigOperators

namespace ArtinMatthews

variable {ι : Type*}

def gamma0PeterssonSourceInfinityPacket (N k : ℕ) [NeZero N] (t : Finset ι)
    (α : ι → ℂ) (n : ι → ℕ+) (z : UpperHalfPlane) : ℂ :=
  ∑ j ∈ t, α j*gamma0PeterssonSourceInfinity N k (n j) z

def gamma0PeterssonSourceInfinityPacketForm (N k : ℕ) [NeZero N]
    (hk : 2 ≤ k) (hEven : Even k) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+) :
    CuspForm (gamma0PeterssonRealGroup N) (k : ℤ) :=
  ∑ j ∈ t, α j • gamma0PeterssonSourceInfinityForm N k hk hEven (n j)

theorem gamma0PeterssonSourceInfinityPacketForm_coe (N k : ℕ) [NeZero N]
    (hk : 2 ≤ k) (hEven : Even k) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+) :
    ⇑(gamma0PeterssonSourceInfinityPacketForm N k hk hEven t α n) =
      gamma0PeterssonSourceInfinityPacket N k t α n := by
  funext z
  simp [gamma0PeterssonSourceInfinityPacketForm,gamma0PeterssonSourceInfinityPacket,
    gamma0PeterssonSourceInfinityForm_coe,smul_eq_mul]

def gamma0PeterssonSourceAtkinPacket (r s : ℕ) [NeZero r] [NeZero s]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (k : ℕ) (t : Finset ι)
    (α : ι → ℂ) (n : ι → ℕ+) (z : UpperHalfPlane) : ℂ :=
  ∑ j ∈ t, α j*gamma0PeterssonSourceAtkin r s hab k (n j) z

def gamma0PeterssonSourceAtkinPacketForm (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1)
    (k : ℕ) (hk : 2 ≤ k) (hEven : Even k) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+) :
    CuspForm (gamma0PeterssonRealGroup (r*s)) (k : ℤ) :=
  ∑ j ∈ t, α j • gamma0PeterssonSourceAtkinForm r s hcop hab k hk hEven (n j)

theorem gamma0PeterssonSourceAtkinPacketForm_coe (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1)
    (k : ℕ) (hk : 2 ≤ k) (hEven : Even k) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+) :
    ⇑(gamma0PeterssonSourceAtkinPacketForm r s hcop hab k hk hEven t α n) =
      gamma0PeterssonSourceAtkinPacket r s hab k t α n := by
  funext z
  simp [gamma0PeterssonSourceAtkinPacketForm,gamma0PeterssonSourceAtkinPacket,
    gamma0PeterssonSourceAtkinForm_coe,smul_eq_mul]

theorem gamma0PeterssonCuspPacket_memLp (N k : ℕ) [NeZero N]
    (F : CuspForm (gamma0PeterssonRealGroup N) (k : ℤ)) :
    MemLp (spectralPeterssonHilbertProfile k F) 2 (volume.restrict (gamma0InteriorRegion N)) := by
  obtain ⟨M,hM⟩ := gamma0PeterssonCuspForm_weighted_bound N k F
  exact gamma0PeterssonHilbertProfile_memLp N k F F.holo'.continuous M hM

end ArtinMatthews
