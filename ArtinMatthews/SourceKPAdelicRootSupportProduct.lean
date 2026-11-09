module

public import ArtinMatthews.SourceKPAdeleLocalCover
public import Mathlib.Data.Finset.NoncommProd


set_option backward.privateInPublic true
@[expose] public section

/-! The finite product of actual one-place lifts retains the cover
phases. Its matrix projections agree with the original matrix at the
selected places and equal the identity everywhere else. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "F" => SourceKPFiniteAdeleCover K hζ
local notation "p" => sourceKPFiniteAdeleProjection K hζ
local notation "ev" => sourceKPAdeleMatrixAt K

def sourceKPAdelicRootSupportFactor (a : A) (P : Pr) : F :=
  sourceKPAdeleLocalCover K hζ P (sourceFiniteKP2Lift K hζ P (ev P a))

local notation "f" => sourceKPAdelicRootSupportFactor K hζ

theorem sourceKPAdelicRootSupportFactor_commute (a : A) {P Q : Pr} (h : P ≠ Q) :
    Commute (f a P) (f a Q) :=
  sourceKPAdeleLocalCover_commute K hζ P Q h.symm _ _

def sourceKPAdelicRootSupportProduct (a : A) (T : Finset Pr) : F :=
  T.noncommProd (f a) fun _ _ _ _ h => sourceKPAdelicRootSupportFactor_commute K hζ a h

local notation "prod" => sourceKPAdelicRootSupportProduct K hζ

theorem sourceKPAdelicRootSupportProduct_insert (a : A) (T : Finset Pr)
    (P : Pr) (hP : P ∉ T) :
    prod a (insert P T) = f a P * prod a T :=
  Finset.noncommProd_insert_of_notMem T P (f a) _ hP

theorem sourceKPAdelicRootSupportProduct_union (a : A) (S T : Finset Pr)
    (h : Disjoint S T) :
    prod a (S ∪ T) = prod a S * prod a T :=
  Finset.noncommProd_union_of_disjoint h (f a) _

theorem sourceKPAdelicRootSupportFactor_at_same (a : A) (P : Pr) :
    ev P (p (f a P)) = ev P a :=
  sourceKPAdeleSingleMatrix_same K P (ev P a)

theorem sourceKPAdelicRootSupportFactor_at_other (a : A) (P Q : Pr) (h : Q ≠ P) :
    ev Q (p (f a P)) = 1 :=
  sourceKPAdeleSingleMatrix_other K P Q h (ev P a)

theorem sourceKPAdelicRootSupportProduct_at (a : A) (T : Finset Pr) (P : Pr) :
    ev P (p (prod a T)) = if P ∈ T then ev P a else 1 := by
  induction T using Finset.induction_on with
  | empty =>
    rw [show prod a (∅ : Finset Pr) = 1 from rfl, map_one p, map_one (ev P),
      ite_eq_right (Finset.notMem_empty P)]
  | insert Q T hQ ih =>
    rw [sourceKPAdelicRootSupportProduct_insert K hζ a T Q hQ, map_mul p, map_mul (ev P), ih]
    by_cases h : P = Q
    · subst Q
      rw [sourceKPAdelicRootSupportFactor_at_same K hζ a P, if_neg hQ, mul_one,
        if_pos (Finset.mem_insert_self P T)]
    · rw [sourceKPAdelicRootSupportFactor_at_other K hζ a Q P h, one_mul]
      simp only [Finset.mem_insert, h, false_or]

theorem sourceKPAdelicRootSupportProduct_at_of_not_mem (a : A) (T : Finset Pr) (P : Pr)
    (hP : P ∉ T) : ev P (p (prod a T)) = 1 := by
  rw [sourceKPAdelicRootSupportProduct_at K hζ a T P, if_neg hP]

end
end ArtinMatthews
