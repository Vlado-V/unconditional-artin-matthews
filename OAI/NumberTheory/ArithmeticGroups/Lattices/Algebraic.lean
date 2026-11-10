module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Solvable
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
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
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! # Algebraic -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Algebraic

noncomputable section

/-!
Concrete affine matrix groups for Lattices. A group is presented as the common
zero set of polynomials inside SL(n), over every extension field. Thus its
point groups and scalar-extension maps are fixed by equations, not by an
uninterpreted arithmetic predicate. Working in SL loses no connected
semisimple linear algebraic groups in characteristic zero: every character,
including the determinant of a faithful representation, is trivial.

Geometric connectedness and semisimplicity use the actual Zariski topology
over an algebraic closure. Semisimplicity means that every connected closed
normal solvable subgroup is trivial. Cocharacters are uniformly polynomial
in t and t⁻¹ over all extension fields. None of these definitions assumes
discreteness, covolume, or compactness of an arithmetic quotient.
-/

open scoped Classical

abbrev SL (n : ℕ) (K : Type) [CommRing K] :=
  Matrix.SpecialLinearGroup (Fin n) K

abbrev CoordinatePolynomial (n : ℕ) (k : Type) [CommRing k] :=
  MvPolynomial (Fin n × Fin n) k

def evaluateMatrix {n : ℕ} {k K : Type} [CommRing k] [CommRing K]
    (ι : k →+* K) (g : SL n K) : CoordinatePolynomial n k →+* K :=
  MvPolynomial.eval₂Hom ι (fun ij => g ij.1 ij.2)

/-- A reduced affine matrix group, described by equations over k.
The supplied subgroup structures assert only closure under the group laws. -/
structure MatrixAlgebraicGroup (k : Type) [Field k] (n : ℕ) where
  equations : Set (CoordinatePolynomial n k)
  subgroup : (K : Type) → [Field K] → (k →+* K) → Subgroup (SL n K)
  mem_iff : ∀ (K : Type) [Field K] (ι : k →+* K) (g : SL n K),
    g ∈ subgroup K ι ↔ ∀ p ∈ equations, evaluateMatrix ι g p = 0

namespace MatrixAlgebraicGroup

variable {k : Type} [Field k] {n : ℕ} (G : MatrixAlgebraicGroup k n)

abbrev Points {K : Type} [Field K] (ι : k →+* K) := ↥(G.subgroup K ι)

abbrev RationalPoints := G.Points (RingHom.id k)

abbrev GeometricPoints := G.Points (algebraMap k (AlgebraicClosure k))

/-- Scalar extension is the entrywise matrix map. -/
def map {K L : Type} [Field K] [Field L] (ι : k →+* K)
    (f : K →+* L) : G.Points ι →* G.Points (f.comp ι) where
  toFun g := ⟨Matrix.SpecialLinearGroup.map f g.val, by
    apply (G.mem_iff L (f.comp ι) _).mpr
    intro p hp
    have h := congrArg f ((G.mem_iff K ι g.val).mp g.property p hp)
    simpa only [evaluateMatrix, MvPolynomial.map_eval₂Hom, map_zero,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] using h⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' g h := by apply Subtype.ext; exact map_mul _ g.val h.val

@[simp] theorem map_entry {K L : Type} [Field K] [Field L]
    (ι : k →+* K) (f : K →+* L) (g : G.Points ι) (i j : Fin n) :
    (G.map ι f g).val i j = f (g.val i j) := rfl

theorem map_injective {K L : Type} [Field K] [Field L]
    (ι : k →+* K) (f : K →+* L) : Function.Injective (G.map ι f) := by
  intro g h he
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  apply f.injective
  exact congrArg (fun x : G.Points (f.comp ι) => x.val i j) he

/-- The prime ideal associated to a geometric point is its evaluation kernel. -/
def geometricPrime (g : G.GeometricPoints) :
    PrimeSpectrum (CoordinatePolynomial n (AlgebraicClosure k)) :=
  ⟨RingHom.ker (evaluateMatrix (RingHom.id _) g.val), RingHom.ker_isPrime _⟩

/-- The ordinary Zariski topology pulled back from the affine coordinate ring. -/
@[instance_reducible] def geometricTopology : TopologicalSpace G.GeometricPoints :=
  TopologicalSpace.induced G.geometricPrime inferInstance

def IsGeometricallyConnected : Prop :=
  @ConnectedSpace G.GeometricPoints G.geometricTopology

def IsSemisimple : Prop :=
  letI : TopologicalSpace G.GeometricPoints := G.geometricTopology
  ∀ N : Subgroup G.GeometricPoints,
    N.Normal → IsClosed (N : Set G.GeometricPoints) →
    IsConnected (N : Set G.GeometricPoints) → Group.IsSolvable N → N = ⊥

/-- A k-defined algebraic homomorphism G_m → G. Uniform polynomial
coordinates in (t,t⁻¹) encode regularity and scalar-extension compatibility. -/
structure Cocharacter where
  hom : (K : Type) → [Field K] → (ι : k →+* K) → (Kˣ →* G.Points ι)
  coordinates : Fin n → Fin n → MvPolynomial (Fin 2) k
  coordinate_eq : ∀ (K : Type) [Field K] (ι : k →+* K)
    (t : Kˣ) (i j : Fin n),
    (hom K ι t).val i j =
      MvPolynomial.eval₂Hom ι
        (fun a : Fin 2 => if a = 0 then (t : K) else ((t⁻¹ : Kˣ) : K))
        (coordinates i j)

/-- Uniform regular coordinates force compatibility with scalar extension. -/
theorem Cocharacter.map_hom (c : G.Cocharacter)
    {K L : Type} [Field K] [Field L] (ι : k →+* K) (f : K →+* L) (t : Kˣ) :
    G.map ι f (c.hom K ι t) = c.hom L (f.comp ι) (Units.map f.toMonoidHom t) := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [map_entry, c.coordinate_eq, c.coordinate_eq, MvPolynomial.map_eval₂Hom]
  apply congrArg (fun x : Fin 2 → L =>
    MvPolynomial.eval₂Hom (f.comp ι) x (c.coordinates i j))
  funext a
  split_ifs <;> rfl

end MatrixAlgebraicGroup

/-- A faithful matrix realization of a connected semisimple k-group. -/
structure ConnectedSemisimpleKGroup (k : Type) [Field k] where
  dimension : ℕ
  matrixGroup : MatrixAlgebraicGroup k dimension
  connected : matrixGroup.IsGeometricallyConnected
  semisimple : matrixGroup.IsSemisimple

/-- k-rank zero: every k-defined cocharacter is trivial. -/
def IsAnisotropic {k : Type} [Field k] (G : ConnectedSemisimpleKGroup k) : Prop :=
  ∀ c : G.matrixGroup.Cocharacter,
    ∀ (K : Type) [Field K] (ι : k →+* K), c.hom K ι = 1

/-- Actual compactness of the group of real points at a specified embedding. -/
def IsCompactAtRealPlace {k : Type} [Field k]
    (G : ConnectedSemisimpleKGroup k) (v : k →+* ℝ) : Prop :=
  CompactSpace (G.matrixGroup.Points v)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Algebraic
