import LambdaRing.Defs

/-! # Ring homomorphisms preserving exterior-power operations -/

/-- A unital ring homomorphism preserving every lambda operation.
Defined for pre-lambda rings, hence also for special lambda rings. -/
structure LambdaRingHom (A B : Type*) [CommRing A] [PreLambdaRing A]
    [CommRing B] [PreLambdaRing B] extends A →+* B where
  map_lambda' : ∀ n a, toFun (LambdaRing.lambda n a) = LambdaRing.lambda n (toFun a)

namespace LambdaRingHom

variable {A B C D : Type*}
variable [CommRing A] [PreLambdaRing A] [CommRing B] [PreLambdaRing B]
variable [CommRing C] [PreLambdaRing C] [CommRing D] [PreLambdaRing D]

instance : FunLike (LambdaRingHom A B) A B where
  coe f := f.toRingHom
  coe_injective := by
    intro f g h
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h

instance : RingHomClass (LambdaRingHom A B) A B where
  map_mul f := f.toRingHom.map_mul
  map_one f := f.toRingHom.map_one
  map_add f := f.toRingHom.map_add
  map_zero f := f.toRingHom.map_zero

@[simp] theorem coe_toRingHom (f : LambdaRingHom A B) : ⇑f.toRingHom = f := rfl

@[simp] theorem map_lambda (f : LambdaRingHom A B) (n : ℕ) (a : A) :
    f (LambdaRing.lambda n a) = LambdaRing.lambda n (f a) := f.map_lambda' n a

@[ext] theorem ext {f g : LambdaRingHom A B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

theorem toRingHom_injective : Function.Injective
    (toRingHom : LambdaRingHom A B → (A →+* B)) := by
  intro f g h
  ext a
  exact DFunLike.congr_fun h a

/-- Identity preserving morphism. -/
protected def id (A : Type*) [CommRing A] [PreLambdaRing A] : LambdaRingHom A A :=
  { RingHom.id A with map_lambda' := fun _ _ => rfl }

@[simp] theorem id_apply (a : A) : LambdaRingHom.id A a = a := rfl

@[simp] theorem toRingHom_id : (LambdaRingHom.id A).toRingHom = RingHom.id A := rfl

/-- Composition of preserving morphisms. -/
def comp (f : LambdaRingHom B C) (g : LambdaRingHom A B) : LambdaRingHom A C :=
  { f.toRingHom.comp g.toRingHom with
    map_lambda' := fun n a => by
      change f (g (LambdaRing.lambda n a)) = LambdaRing.lambda n (f (g a))
      rw [map_lambda, map_lambda] }

@[simp] theorem comp_apply (f : LambdaRingHom B C) (g : LambdaRingHom A B) (a : A) :
    f.comp g a = f (g a) := rfl

@[simp] theorem toRingHom_comp (f : LambdaRingHom B C) (g : LambdaRingHom A B) :
    (f.comp g).toRingHom = f.toRingHom.comp g.toRingHom := rfl

@[simp] theorem id_comp (f : LambdaRingHom A B) : (LambdaRingHom.id B).comp f = f := by
  ext a
  rfl

@[simp] theorem comp_id (f : LambdaRingHom A B) : f.comp (LambdaRingHom.id A) = f := by
  ext a
  rfl

theorem comp_assoc (f : LambdaRingHom C D) (g : LambdaRingHom B C)
    (h : LambdaRingHom A B) : (f.comp g).comp h = f.comp (g.comp h) := by
  ext a
  rfl

end LambdaRingHom
