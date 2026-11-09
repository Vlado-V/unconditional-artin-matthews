module

public import ArtinMatthews.SourceJacquetAdditiveTranslation


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite additive quotient of a compact Jacquet ball by
a smaller open ball. Representatives are chosen from the actual
quotient, and equality of classes is exactly the valuation bound
on the difference. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SourcePhysical
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))

abbrev sourceJacquetUpperBall (R : ℕ) := sourceLocalOpenBall K P (R : ℤ)

def sourceJacquetUpperKernel (R M : ℕ) : AddSubgroup (sourceJacquetUpperBall K P R) :=
  (sourceLocalOpenBall K P (-(M : ℤ))).toAddSubgroup.comap (sourceJacquetUpperBall K P R).toAddSubgroup.subtype

abbrev SourceJacquetUpperQuotient (R M : ℕ) :=
  sourceJacquetUpperBall K P R ⧸ sourceJacquetUpperKernel K P R M

theorem sourceJacquetUpperQuotient_finite (R M : ℕ) : Finite (SourceJacquetUpperQuotient K P R M) := by
  let U := sourceJacquetUpperBall K P R
  let H := sourceJacquetUpperKernel K P R M
  have hU : IsCompact (U : Set (P.adicCompletion K)) := sourceLocalBall_isCompact K P (R : ℤ)
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have hH : IsOpen (H : Set U) := (sourceLocalBall_isOpen K P (-(M : ℤ))).preimage continuous_subtype_val
  exact AddSubgroup.quotient_finite_of_isOpen H hH

def sourceJacquetUpperReduction (R M : ℕ) : sourceJacquetUpperBall K P R →+ SourceJacquetUpperQuotient K P R M :=
  QuotientAddGroup.mk' _

theorem sourceJacquetUpperReduction_surjective (R M : ℕ) :
    Function.Surjective (sourceJacquetUpperReduction K P R M) := QuotientAddGroup.mk'_surjective _

theorem sourceJacquetUpperReduction_eq_iff (R M : ℕ) (x y : sourceJacquetUpperBall K P R) :
    sourceJacquetUpperReduction K P R M x = sourceJacquetUpperReduction K P R M y ↔
      sourceLocalValuation K P ((y : P.adicCompletion K) - (x : P.adicCompletion K)) ≤ WithZero.exp (-(M : ℤ)) := by
  let r := sourceJacquetUpperReduction K P R M
  have hq : r (y - x) = 0 ↔ y - x ∈ sourceJacquetUpperKernel K P R M := QuotientAddGroup.eq_zero_iff _
  calc
    r x = r y ↔ r (y - x) = 0 := by rw [map_sub, sub_eq_zero, eq_comm]
    _ ↔ _ := hq

def sourceJacquetUpperRepresentative (R M : ℕ) (a : SourceJacquetUpperQuotient K P R M) :
    sourceJacquetUpperBall K P R :=
  (sourceJacquetUpperReduction_surjective K P R M a).choose

theorem sourceJacquetUpperRepresentative_class (R M : ℕ) (a : SourceJacquetUpperQuotient K P R M) :
    sourceJacquetUpperReduction K P R M (sourceJacquetUpperRepresentative K P R M a) = a :=
  (sourceJacquetUpperReduction_surjective K P R M a).choose_spec

end
end ArtinMatthews
