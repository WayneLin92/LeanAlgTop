import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Basic
import Mathlib.Deprecated.Subgroup
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.Span
import Mathlib.LinearAlgebra.Quotient
import Mathlib.Order.Directed
import Mathlib.Algebra.Module.Equiv

open Set Function Submodule

variable {R :Type _}[Ring R]{X :Type _}[AddCommGroup X][Module R X]

theorem Submodule_modularprop (A B C : Submodule R X)(v: A ≤ C) : (A + B) ⊓ C = A + (B ⊓ C) := by
  apply sup_inf_assoc_of_le
  exact v

theorem Submodule_exchange_limit1 {I:Type _}[Nonempty I](C:I → Submodule R X)(p: Directed (fun x x1 => x ≤ x1) C)(A B : Submodule R X): ⨆ i:I ,(A + C i ⊓  B) = A + (⨆ i : I ,C i) ⊓ B := by
  apply le_antisymm
  apply iSup_le
  intro i
  apply sup_le_sup_left
  apply inf_le_inf_right
  apply le_iSup
  apply sup_le
  have i:I := Classical.ofNonempty
  apply le_trans
  swap
  apply le_iSup 
  exact i
  simp
  intro x p
  cases' p with p1 p2
  simp at p1 p2
  rw [Submodule.mem_iSup_of_directed C p] at p1
  cases' p1 with i p1
  apply mem_iSup_of_mem
  swap 
  exact i
  apply mem_sup_right
  constructor
  repeat assumption
  
theorem Submodule_exchange_limit2 {I: Type}{i0:I}(C:I → Submodule R X)(p: IsMinOn C univ i0)(A B : Submodule R X): ⨅ i:I ,(A + C i ⊓  B)= A+ (⨅ i:I ,C i) ⊓  B := by
  have p1: ⨅ i:I ,(A + C i ⊓  B) = A+C i0⊓ B
  apply le_antisymm
  apply iInf_le
  apply le_iInf
  intro i
  apply sup_le_sup_left
  apply inf_le_inf_right
  apply p
  simp
  have p2: ⨅ i:I ,C i=C i0
  apply le_antisymm
  apply iInf_le
  apply le_iInf
  intro i
  apply p
  simp
  rw [p1,p2]

def Submodule_Quotient_denominator (A B:Submodule R X): Submodule R B := by
  repeat constructor; swap
  exact {x | Subtype.val x ∈ A }
  simp
  intro a _ b _
  apply AddSubsemigroup.add_mem'
  simp
  simp
  intro r a _
  apply smul_mem

def Submodule_Quotient (A B:Submodule R X) : Type _ := B⧸Submodule_Quotient_denominator A B

instance Submodule_Quotient_AddCommMonoid (A B : Submodule R X) : AddCommMonoid (Submodule_Quotient A B) := by
  unfold Submodule_Quotient
  infer_instance

instance Submodule_Quotient_Module (A B : Submodule R X) : Module R (Submodule_Quotient  A B) := by
  unfold Submodule_Quotient
  infer_instance

def isomorphism_term1 (N H :Submodule R X) : Type _ := Submodule_Quotient  (H ⊓ N) H

instance isomorphism_term1_addcommgroup (N H :Submodule R X) : AddCommMonoid (isomorphism_term1  N H) := by
  unfold isomorphism_term1
  infer_instance

instance isomorphism_term1_module (N H :Submodule R X) : Module R (isomorphism_term1  N H) := by
  unfold isomorphism_term1
  infer_instance

def isomorphism_term2 (N H :Submodule R X) : Type _ := Submodule_Quotient N (H+N)

instance isomorphism_term2_addcommgroup (N H :Submodule R X) : AddCommMonoid (isomorphism_term2  N H) := by
  unfold isomorphism_term2
  infer_instance

instance isomorphism_term2_module (N H :Submodule R X) : Module R (isomorphism_term2  N H) := by
  unfold isomorphism_term2
  infer_instance

def isomorphism_hom (N H :Submodule R X) : isomorphism_term1 N H → isomorphism_term2  N H := by
  unfold isomorphism_term1
  apply Quotient.lift
  swap
  intro a
  have p:= Subtype.mem a
  unfold isomorphism_term2
  apply Quotient.mk
  constructor
  swap
  exact (Subtype.val a:X)
  simp
  apply mem_sup_left
  exact p
  simp
  intro a _ b _ p
  rw [Quotient.mk,Quotient.mk,Quot.eq]
  unfold HasEquiv.Equiv at p
  unfold instHasEquiv at p
  simp at p
  rw [quotientRel_r_def] at p
  apply EqvGen.rel
  rw [quotientRel_r_def]
  unfold Submodule_Quotient_denominator
  simp
  unfold Submodule_Quotient_denominator at p
  simp at p
  exact p

theorem isomorphism_hom_linear (N H :Submodule R X) : IsLinearMap R (isomorphism_hom  N H):= by
  constructor
  unfold isomorphism_hom
  apply Quotient.ind₂
  intro a b
  rfl
  unfold isomorphism_hom
  intro r
  apply Quotient.ind
  intro a
  rfl

theorem isomorphism_hom_bijective (N H :Submodule R X) : Bijective (isomorphism_hom  N H):= by 
  constructor
  unfold Injective
  apply Quotient.ind₂
  intro a b p
  unfold isomorphism_hom at p
  simp at p
  unfold Quotient.mk at p
  unfold Quotient.lift at p
  simp at p
  rw [Submodule.Quotient.eq] at p
  unfold Submodule_Quotient_denominator at p
  simp at p
  rw [Quotient.mk,Quotient.mk,Quot.eq]
  apply EqvGen.rel
  rw [quotientRel_r_def]
  unfold Submodule_Quotient_denominator
  simp
  exact p
  unfold Surjective
  apply Quotient.ind
  intro a
  have p:=Subtype.mem a
  simp at p
  rw [mem_sup] at p
  rcases p with ⟨y, p, z, q, w⟩
  use Quotient.mk _ (Subtype.mk y p)
  unfold isomorphism_hom
  simp
  unfold Quotient.mk
  unfold Quotient.lift
  simp
  rw [Submodule.Quotient.eq]
  unfold Submodule_Quotient_denominator
  simp
  have :z=↑a-y
  rw [← w]
  simp
  rw [this] at q
  have :y- ↑a∈ N
  swap
  exact this
  have : y-↑a=-(↑a-y)
  simp
  rw [this]
  apply neg_mem
  exact q

noncomputable def isomorphism_equiv (N H :Submodule R X) : isomorphism_term1 N H ≃ₗ[R] isomorphism_term2 N H := by
  apply LinearEquiv.ofBijective
  swap
  apply IsLinearMap.mk'
  swap
  exact isomorphism_hom N H
  exact isomorphism_hom_linear N H
  exact isomorphism_hom_bijective N H

def Butterfly (A B C D: Submodule R X): Type _ := Submodule_Quotient (C + (A ⊓ D)) (C + (B ⊓ D))

instance Butterfly_addcommmonoid (A B C D: Submodule R X) : AddCommMonoid (Butterfly A B C D) := by
  unfold Butterfly
  infer_instance

instance Butterfly_module (A B C D: Submodule R X) : Module R (Butterfly A B C D) := by
  unfold Butterfly
  infer_instance

def Butterfly' (A B C D: Submodule R X): Type _ := Submodule_Quotient  (B⊓ C+A⊓ D) (B⊓ D)

instance Butterfly'_addcommmonoid (A B C D: Submodule R X) : AddCommMonoid (Butterfly' A B C D) := by
  unfold Butterfly'
  infer_instance

instance Butterfly'_module (A B C D: Submodule R X) : Module R (Butterfly'  A B C D) := by
  unfold Butterfly'
  infer_instance 

theorem Lattice_lemma1 {X:Type _}[Lattice X][IsModularLattice X](A B C D: X)(v:A ≤ B)(w:C ≤ D):(B ⊓ D) ⊓ (C ⊔ A ⊓ D)=B ⊓ C ⊔ A ⊓ D := by
  conv => left; rw [inf_assoc]; right ;rw [inf_comm,sup_comm]
  rw [sup_inf_assoc_of_le]
  swap 
  apply inf_le_right
  rw [inf_comm,sup_inf_assoc_of_le]
  swap
  apply le_trans
  apply inf_le_left
  assumption
  rw [sup_comm,inf_comm]
  congr
  rw [inf_eq_left]
  assumption

theorem Lattice_lemma2 {X:Type _}[Lattice X][IsModularLattice X](A B C D: X)(v:A ≤ B): (B ⊓ D) ⊔ (C ⊔ A ⊓ D)= C ⊔ B ⊓ D := by
  rw [sup_comm, sup_assoc]
  congr
  simp
  apply le_trans
  apply inf_le_left
  assumption

def LinearEquiv.quotientModuleMap {X': Type _ }[AddCommGroup X'][Module R X'](e: X≃ₗ[R] X')(A:Submodule R X)(A':Submodule R X')(f:A'= map e A) : @HasQuotient.Quotient X (Submodule R X) _ A ≃ₗ[R] X'⧸ A' := by
  constructor
  pick_goal 4
  apply Quotient.lift
  swap
  intro x
  apply Quotient.mk
  exact e.invFun x
  intro a b p
  unfold Quotient.mk
  rw [Quot.eq]
  apply EqvGen.rel
  rw [quotientRel_r_def]
  unfold HasEquiv.Equiv at p
  unfold instHasEquiv at p
  simp at p
  rw [quotientRel_r_def] at p
  simp at p
  rw [f] at p
  rcases p with ⟨y,p1,p2⟩
  have :invFun e (a-b)=invFun e a -invFun e b
  simp
  rw [← this,← p2]
  simp
  assumption
  pick_goal 3
  repeat constructor;swap
  apply Quotient.lift
  swap
  intro x
  apply Quotient.mk
  exact e x
  intro a b p
  unfold Quotient.mk
  rw [Quot.eq]
  apply EqvGen.rel
  rw [quotientRel_r_def]
  unfold HasEquiv.Equiv at p
  unfold instHasEquiv at p
  simp at p
  rw [quotientRel_r_def] at p
  simp at p
  rw [f]
  simp
  use a-b
  simp
  assumption
  apply Quotient.ind₂
  intro a b
  unfold Quotient.mk
  unfold Quotient.lift
  have :∃c,c=a+b
  use a+b
  cases' this with c this1
  have : @HAdd.hAdd (X ⧸ A) (X ⧸ A) (X ⧸ A) instHAdd (Quot.mk (@Setoid.r X (quotientRel A)) a) (Quot.mk (@Setoid.r X (quotientRel A)) b)=Quot.mk (@Setoid.r X (quotientRel A)) c
  rw [this1]
  simp
  rw [this]
  simp
  rw [this1]
  simp
  simp
  intro r
  apply Quotient.ind
  intro a
  unfold Quotient.mk
  unfold Quotient.lift
  have :∃c,c=r•a
  use r•a
  cases' this with c this1
  have : @HSMul.hSMul R (X ⧸ A) (X ⧸ A) instHSMul r (Quot.mk _ a)=Quot.mk _ c
  rw [this1]
  simp
  rw [this]
  simp
  rw [this1]
  simp
  simp
  unfold LeftInverse
  apply Quotient.ind
  intro a
  unfold Quotient.mk
  unfold Quotient.lift
  simp
  simp
  unfold Function.RightInverse
  unfold LeftInverse
  apply Quotient.ind
  intro a
  unfold Quotient.mk
  unfold Quotient.lift
  simp

theorem Butterfly'_equiv_isomorphism_term1 (A B C D: Submodule R X)(v:A ≤ B)(w:C ≤ D) :Butterfly'  A B C D≃ₗ[R]  isomorphism_term1  (C + A ⊓ D) (B ⊓ D) := by 
  apply LinearEquiv.quotientModuleMap
  swap
  rfl
  simp
  rw [Lattice_lemma1]
  ext x
  simp
  repeat assumption

theorem Butterfly'_equiv_Butterfly_isomorphism_term2 (A B C D: Submodule R X)(v:A ≤ B) :Butterfly A B C D ≃ₗ[R]  isomorphism_term2 (C + A ⊓ D) (B ⊓ D) := by
  apply LinearEquiv.quotientModuleMap
  swap
  apply LinearEquiv.ofEq
  simp
  rw [Lattice_lemma2]
  assumption
  ext x
  unfold Submodule_Quotient_denominator
  simp
  constructor
  intro p
  use x
  constructor
  exact p
  have : C ⊔ A ⊓ D ≤  C ⊔ B ⊓ D
  apply sup_le_sup_left
  apply inf_le_inf_right
  exact v
  use this p
  rfl
  intro p
  rcases p with ⟨y,q1,q2,r⟩
  have : @FunLike.coe ({ x // x ∈ C ⊔ B ⊓ D } ≃ₗ[R] { x // x ∈ B ⊓ D ⊔ (C ⊔ A ⊓ D) }) { x // x ∈ C ⊔ B ⊓ D } (fun _ => { x // x ∈ B ⊓ D ⊔ (C ⊔ A ⊓ D) }) AddHomClass.toFunLike (LinearEquiv.ofEq (C + B ⊓ D) (B ⊓ D + (C + A ⊓ D)) (_ : C + B ⊓ D = B ⊓ D + (C + A ⊓ D))) { val := y, property := (_ : y ∈ C ⊔ B ⊓ D) } = y 
  rfl
  rw [r] at this
  rw [this]
  exact q1

noncomputable def Butterfly'_equiv_Butterfly (A B C D: Submodule R X)(v:A ≤ B)(w:C ≤ D) : Butterfly' A B C D ≃ₗ[R] Butterfly A B C D := by
  apply @LinearEquiv.trans R R R (Butterfly' A B C D) (isomorphism_term1 (C + A ⊓ D) (B ⊓ D)) (Butterfly A B C D) _ _ _ _ _ _ _ _ _ (RingHom.id R) (RingHom.id R) (RingHom.id R) (RingHom.id R) (RingHom.id R) (RingHom.id R) _ _ _ _ _ _ _
  apply Butterfly'_equiv_isomorphism_term1
  pick_goal 3
  apply @LinearEquiv.trans R R R (isomorphism_term1 (C + A ⊓ D) (B ⊓ D)) (isomorphism_term2 (C + A ⊓ D) (B ⊓ D)) (Butterfly A B C D) _ _ _ _ _ _ _ _ _ (RingHom.id R) (RingHom.id R) (RingHom.id R) (RingHom.id R) (RingHom.id R) (RingHom.id R) _ _ _ _ _ _ _
  apply isomorphism_equiv
  symm
  apply Butterfly'_equiv_Butterfly_isomorphism_term2
  repeat assumption

def Butterfly'_symm_equiv (A B C D: Submodule R X) :Butterfly'  A B C D ≃ₗ[R] Butterfly' C D A B
:= by
  apply LinearEquiv.quotientModuleMap
  swap
  apply LinearEquiv.ofEq
  apply inf_comm
  ext x
  simp
  constructor
  intro p
  use x
  have := Subtype.mem x
  simp at this
  rw [and_comm] at this
  use this
  constructor
  unfold Submodule_Quotient_denominator
  simp
  unfold Submodule_Quotient_denominator at p
  simp at p
  rw [inf_comm,sup_comm,inf_comm]
  exact p
  rfl
  intro p
  rcases p with ⟨y,h,p⟩
  cases' p with p1 p2
  unfold Submodule_Quotient_denominator at p1 
  simp at p1
  unfold Submodule_Quotient_denominator
  simp
  have : @FunLike.coe ({ x // x ∈ B ⊓ D } ≃ₗ[R] { x // x ∈ D ⊓ B }) { x // x ∈ B ⊓ D } (fun _ => { x // x ∈ D ⊓ B }) AddHomClass.toFunLike (LinearEquiv.ofEq (B ⊓ D) (D ⊓ B) (_ : B ⊓ D = D ⊓ B)) { val := y, property := @Iff.mpr (y ∈ B ⊓ D) (y ∈ B ∧ y ∈ D) (Iff.of_eq _ ) h } = y
  rfl
  rw [p2] at this
  rw [this]
  rw [inf_comm,sup_comm,inf_comm]
  exact p1
  simp

noncomputable def Butterfly_symm_equiv (A B C D: Submodule R X)(v:A ≤ B)(w:C ≤ D) : Butterfly  A B C D ≃ₗ[R] Butterfly C D A B := by
  apply @LinearEquiv.trans R R R (Butterfly A B C D) (Butterfly' A B C D) (Butterfly C D A B) _ _ _ _ _ _ _ _ _ (RingHom.id R) (RingHom.id R) (RingHom.id R) (RingHom.id R) (RingHom.id R) (RingHom.id R) _ _ _ _ _ _ _
  symm
  apply Butterfly'_equiv_Butterfly
  repeat assumption
  apply @LinearEquiv.trans R R R (Butterfly' A B C D) (Butterfly' C D A B) (Butterfly C D A B) _ _ _ _ _ _ _ _ _ (RingHom.id R) (RingHom.id R) (RingHom.id R) (RingHom.id R) (RingHom.id R) (RingHom.id R) _ _ _ _ _ _ _
  apply Butterfly'_symm_equiv
  apply Butterfly'_equiv_Butterfly
  repeat assumption

variable {X': Type _}[AddCommGroup X'][Module R X']{f:X→ₗ[R] X'}

def Butterfly_functorial {A B C D:Submodule R X}{A' B' C' D':Submodule R X'}(fA: f '' A ≤  A')(fB: f '' B ≤ B')(fC: f '' C ≤ C')(fD: f '' D ≤ D'): Butterfly  A B C D → Butterfly A' B' C' D':= by
  apply Quotient.lift
  swap
  intro x
  apply Quotient.mk
  constructor
  swap
  exact f x
  have p:=Subtype.mem x
  simp at p
  rw [mem_sup] at p
  rcases p with ⟨y,p1,z,p2,p3⟩  
  simp
  rw [mem_sup]
  use f y
  constructor
  apply fC
  apply mem_image_of_mem
  assumption
  use f z
  constructor
  constructor
  apply fB
  apply mem_image_of_mem
  exact p2.1
  apply fD
  apply mem_image_of_mem
  exact p2.2
  rw [← p3]
  simp
  intro a b p
  rw [Quotient.mk,Quotient.mk,Quot.eq]
  unfold HasEquiv.Equiv at p
  unfold instHasEquiv at p
  simp at p
  rw [quotientRel_r_def] at p
  apply EqvGen.rel
  rw [quotientRel_r_def]
  unfold Submodule_Quotient_denominator
  simp
  unfold Submodule_Quotient_denominator at p
  simp at p
  rw [mem_sup]
  rw [mem_sup] at p
  rcases p with ⟨y,p1,z,p2,p3⟩
  use f y
  constructor
  apply fC
  apply mem_image_of_mem
  assumption
  use f z
  constructor
  constructor
  apply fA
  apply mem_image_of_mem
  exact p2.1
  apply fD
  apply mem_image_of_mem
  exact p2.2
  have :f ↑a -f ↑b = f (↑a - ↑b)
  simp
  rw [this,← p3]
  simp

theorem Butterfly_functorial_linear {A B C D:Submodule R X}{A' B' C' D':Submodule R X'}(fA: f '' A≤  A')(fB: f '' B≤ B')(fC: f '' C≤ C')(fD: f '' D≤ D'): IsLinearMap R (Butterfly_functorial fA fB fC fD) := by
  constructor
  unfold Butterfly_functorial
  apply Quotient.ind₂
  intro a b
  have : ∃c, c=a+b∧ Quotient.mk (quotientRel (Submodule_Quotient_denominator (C + A ⊓ D) (C + B ⊓ D))) c=@HAdd.hAdd (Butterfly A B C D) (Butterfly A B C D) (Butterfly A B C D) instHAdd (Quotient.mk (quotientRel (Submodule_Quotient_denominator (C + A ⊓ D) (C + B ⊓ D))) a) (Quotient.mk (quotientRel (Submodule_Quotient_denominator (C + A ⊓ D) (C + B ⊓ D))) b)
  use (a+b)
  simp
  rfl
  rcases this with ⟨c,this1,this2⟩
  rw [← this2]

  unfold Quotient.mk
  unfold Quotient.lift
  simp
  rw [this1,← Submodule.Quotient.mk_add]
  congr
  simp
  unfold Butterfly_functorial
  intro r
  apply Quotient.ind
  intro a
  
  have :∃c, c= r• a∧ Quotient.mk (quotientRel (Submodule_Quotient_denominator (C + A ⊓ D) (C + B ⊓ D))) c=@HSMul.hSMul R (Butterfly A B C D) (Butterfly A B C D) instHSMul r (Quotient.mk (quotientRel (Submodule_Quotient_denominator (C + A ⊓ D) (C + B ⊓ D))) a) 
  use r•a
  simp
  rfl
  rcases this with ⟨c,this1,this2⟩
  rw [← this2]
  unfold Quotient.mk
  unfold Quotient.lift
  simp
  rw [this1,← Submodule.Quotient.mk_smul]
  congr
  simp

theorem Butterfly_functorial_surjective {A B C D:Submodule R X}{A' B' C' D':Submodule R X'}(fA: f '' A≤  A')(fB: f '' B≤ B')(fC: f '' C≤ C')(fD: f '' D≤ D')(p : f '' (B⊓D)=B'⊓ D'):Surjective (Butterfly_functorial fA fB fC fD) := by
  unfold Surjective
  apply Quotient.ind
  intro b
  have q:= Subtype.mem b
  simp at q
  rw [mem_sup] at q
  rcases q with ⟨y,q1,z,q2,q3⟩
  have q2 : z ∈ f '' (B⊓ D)
  rw [p]
  exact q2
  simp at q2
  rcases q2  with ⟨x,q2,q4⟩ 
  have : x∈ C+B⊓D
  simp
  rw [mem_sup]
  use 0
  simp
  exact q2
  use Quotient.mk _ (Subtype.mk x this)
  unfold Butterfly_functorial
  unfold Quotient.lift
  unfold Quotient.mk
  simp
  rw [Submodule.Quotient.eq]
  unfold Submodule_Quotient_denominator
  simp
  rw [q4,← q3]
  simp
  rw [mem_sup]
  use y
  constructor
  assumption
  use 0
  simp

theorem Butterfly_functorial_injective {A B C D:Submodule R X}{A' B' C' D':Submodule R X'}(fA: f '' A≤  A')(fB: f '' B≤ B')(fC: f '' C≤ C')(fD: f '' D≤ D')(w:C≤ D)(w':C'≤ D')(p:f ⁻¹' ((C'+A').carrier)=(C+A).carrier): Injective (Butterfly_functorial fA fB fC fD):= by
  unfold Injective
  apply Quotient.ind₂
  intro a b q
  unfold Butterfly_functorial at q
  unfold Quotient.mk at q
  unfold Quotient.lift at q
  simp at q
  rw [Submodule.Quotient.eq] at q
  unfold Submodule_Quotient_denominator at q
  simp at q
  unfold Quotient.mk

  rw [Quot.eq]
  apply EqvGen.rel
  rw [quotientRel_r_def]
  unfold Submodule_Quotient_denominator 
  simp
  conv => rhs;  rw [← Submodule.add_eq_sup,← Submodule_modularprop C A D w]
  conv at q => rhs; rw [← Submodule.add_eq_sup,← Submodule_modularprop C' A' D' w']
  cases' q with q1 q2
  
  constructor
  have : (@Subtype.val X (fun x => x ∈ ↑(C + B ⊓ D)) a )-↑b ∈ (C+A).carrier
  rw [← p]
  simp
  exact q1
  exact this
  have pa:=Subtype.mem a
  have pb:=Subtype.mem b
  simp at pa pb
  conv at pa => rhs;  rw [← Submodule.add_eq_sup,← Submodule_modularprop C B D w]
  conv at pb => rhs;  rw [← Submodule.add_eq_sup,← Submodule_modularprop C B D w]
  apply sub_mem
  exact pa.2
  exact pb.2

theorem Butterfly_functorial_bijective {A B C D:Submodule R X}{A' B' C' D':Submodule R X'}(fA: f '' A≤  A')(fB: f '' B≤ B')(fC: f '' C≤ C')(fD: f '' D≤ D')(w:C≤ D)(w':C'≤ D')(α : f '' A =  A')(β :f '' B= B')(γ : C= f⁻¹' C')(δ : D = f ⁻¹' D') : Bijective (Butterfly_functorial fA fB fC fD) := by
  constructor
  apply Butterfly_functorial_injective
  pick_goal 3
  ext x
  simp
  constructor
  intro p
  rw [mem_sup] at p
  rcases p with ⟨y,p1,z,p2,p3⟩
  have p2: z∈ f '' A
  rw [α]
  exact p2 
  simp at p2
  rcases p2 with ⟨z1,p2,p4⟩
  have p3: y = f (x-z1)
  simp 
  rw [← p3,p4]
  simp
  rw [p3] at p1
  have p5: x-z1∈ @SetLike.coe (Submodule R X) X setLike C
  rw [γ]
  simp
  simp at p1
  exact p1
  rw [mem_sup]
  use (x-z1)
  constructor
  exact p5
  use z1
  simp
  exact p2
  intro p
  rw [mem_sup]
  rw [mem_sup] at p
  rcases p with ⟨y,p1,z,p2,p3⟩
  use f y
  constructor
  apply fC
  apply mem_image_of_mem
  exact p1
  use f z
  constructor
  apply fA
  apply mem_image_of_mem
  exact p2
  rw [← p3] 
  simp
  pick_goal 3
  apply Butterfly_functorial_surjective
  ext x
  constructor
  intro p
  simp at p
  rcases p with ⟨x1,p1,p2⟩
  constructor
  apply fB
  simp
  use x1
  tauto
  apply fD
  simp
  use x1
  tauto
  intro p
  cases' p with p1 p2
  rw [←  β ] at p1
  simp at p1
  rcases p1 with ⟨y, p1, p3⟩
  simp
  use y
  rw [p3]
  simp
  constructor
  exact p1
  show y ∈ @SetLike.coe (Submodule R X) X setLike D
  rw [δ ]
  simp
  rw [p3]
  exact p2
  repeat assumption

noncomputable def Butterfly_functorial_equiv {A B C D:Submodule R X}{A' B' C' D':Submodule R X'}(fA: f '' A≤  A')(fB: f '' B≤ B')(fC: f '' C≤ C')(fD: f '' D≤ D')(w:C≤ D)(w':C'≤ D')(α : f '' A =  A')(β :f '' B= B')(γ : C= f⁻¹' C')(δ : D = f ⁻¹' D') : Butterfly  A B C D ≃ₗ[R] Butterfly A' B' C' D' := by
  apply LinearEquiv.ofBijective
  swap
  apply IsLinearMap.mk'
  swap
  apply Butterfly_functorial 
  repeat assumption
  apply Butterfly_functorial_linear
  repeat assumption
  apply Butterfly_functorial_bijective
  repeat assumption
