module frp where

-- First, some imports from the standard library...

open import Data.Unit
open import Data.Nat hiding (_⊔_; _*_)
open import Data.Product hiding (<_,_>; curry; uncurry)
open import Data.List hiding ([_]; _++_)
open import Level hiding (zero; suc)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Core

-- First, we'll define our functor category Set^ℕ. The objects
-- are nat-indexed families of (small) sets.

Obj : Set₁
Obj = ℕ → Set

-- The morphisms between objects are families of maps. These
-- are really natural transformations, but because there are
-- no interesting arrows in ℕ, the naturality conditions are
-- trivial/nonexistent in this case.

Hom : Obj × Obj → Set
Hom (A , B) = (n : ℕ) → A n → B n 

-- We also define identity and composition for this category.

id : {A : Obj} → Hom(A , A)
id n a = a 

_·_ : {A B C : Obj} → Hom(A , B) → Hom(B , C) → Hom(A , C)
(f · g) = λ n a → g n (f n a)

infixr 2 _·_

-- Now that we've defined our category of interest,
-- let's proceed by defining the categorical structure
-- we will use to interpret the language 

--
-- First, we define the terminal object of Set^ℕ.
-- This is just the unit at every instant. 

I : Obj
I n = ⊤

-- We also define the map ∗ which is the unique map into
-- the terminal object. Proofs of the relevant universal
-- properties are at the end of the file. 

∗ : {A : Obj} → Hom (A , I)
∗ n = λ n → tt

-- Next, we define products. As with the terminal
-- object, products are defined pointwise. 

_⊗_ : Obj → Obj → Obj
A ⊗ B = λ n → A n × B n

infixr 2 _⊗_

-- The pairing operation (which Jeremy Gibbons calls "fork")
-- takes two morphisms from A and returns a single morphism
-- returning a product. This constructs pairs pointwise in the
-- obvious way.

<_,_> : {A B C : Obj} → 
        Hom(A , B) → Hom(A , C) → Hom(A , (B ⊗ C))
< f , g > n a = (f n a , g n a)

-- Likewise, the projections are defined pointwise as well. 

fst : {A B : Obj} → Hom((A ⊗ B) , A)
fst n (a , b) = a

snd : {A B : Obj} → Hom((A ⊗ B) , B)
snd n (a , b) = b

-- It is also sometimes convenient to have the definition of
-- the functorial action for the product type to hand.

_⊗'_ : {A B C D : Obj} → 
       Hom(A , B) → 
       Hom(C , D) → 
       Hom((A ⊗ C) , (B ⊗ D))
f ⊗' g = < fst · f , snd · g >

--
-- Now we define exponentials (i.e., function types). As with
-- units and products, this is defined pointwise
-- 

_⇒_ : Obj → Obj → Obj
A ⇒ B = λ n → A n → B n


-- Exponentials are right adjoint to products. This means that
-- Hom((A ⊗ B) , C) should be isomorphic to Hom (A , B ⇒ C).
-- So we give the two sides of this isomorphism below. 

curry : {A B C : Obj} → Hom((A ⊗ B) , C) → Hom (A , B ⇒ C)
curry f n a b = f n (a , b)

uncurry : {A B C : Obj} → Hom (A , B ⇒ C) → Hom((A ⊗ B) , C)
uncurry f n (a , b) = f n a b

-- We also define the functorial action for A ⇒ B. 

_⇒'_ : {A B X Y : Obj} → 
        Hom(A , B) → Hom(X , Y) → Hom((B ⇒ X) , (A ⇒ Y))
(f ⇒' g) n h a = g n (h (f n a))

--
-- Now, we define the delay operator • A. It is the unit type
-- ⊤ at time 0, and is the A n at time n + 1.
-- 

• : Obj → Obj
• A 0       = ⊤
• A (suc n) = A n

-- We also define the functorial action below. 

•' : {A B : Obj} → Hom(A , B) → Hom(• A , • B)
•' f zero a    = tt
•' f (suc n) a = f n a

-- In addition to being a functor, •_ is a monoidal functor
-- with respect to products. In fact, there is a monoidal
-- isomorphism, and we give both sides below. 

•-ε : Hom(I , • I)
•-ε zero tt = tt
•-ε (suc n) tt = tt

•-ε' : Hom(• I , I)
•-ε' n _ = tt

•-φ : {A  B : Obj} → Hom ((• A ⊗ • B) , • (A ⊗ B))
•-φ zero    (tt , tt) = tt
•-φ (suc n) (a , b)   = (a , b)

•-φ' : {A  B : Obj} → Hom (• (A ⊗ B) , (• A ⊗ • B))
•-φ' zero    tt      = (tt , tt) 
•-φ' (suc n) (a , b)  = (a , b)

-- To define the □A modality, we make use of the fact that
-- every comonad arises as an adjunction. In this case, we
-- use the adjunction between Set^N and Set. To define this
-- adjunction, we give the two adjoint functors below. 

-- A Set can be turned into a type by the constant functor. 

F : Set → Obj
F X = λ n → X 

F' : {X Y : Set} → (X → Y) → Hom(F X , F Y)
F' f n x = f x

-- A Obj can be made into a set via the "global elements"
-- functor.  This sends a family of Sets A_n to a single
-- dependent function space Πn:N. A_n

G : Obj → Set
G A = (n : ℕ) → A n

G' : {A B : Obj} → Hom(A , B) → (G A → G B)
G' f a n = f n (a n)

-- To show that these two functors form an adjunction, we give
-- an isomorphism between maps in set (ie, functions X → G A)
-- and maps in the functor category (ie, elements of Hom(F X,
-- A).

adj : {A : Obj} {X : Set} → Hom(F X , A) → X → G A
adj f x = λ n → f n x

adj' : {A : Obj} {X : Set} → (X → G A) → Hom(F X , A)
adj' f n = λ x → f x n

-- Now we can define the comonad and its functorial action as
-- the composition of functors.

□ : Obj → Obj
□ A = F (G A)

□' : {A B : Obj} → Hom(A , B) → Hom(□ A , □ B)
□' f = F' (G' f)

-- The □A modality is also a monoidal functor with respect to
-- the the product structure.

□-ε : Hom(I , □ I)
□-ε = λ n _ n₁ → tt

□-φ : {A  B : Obj} → Hom ((□ A ⊗ □ B) , □ (A ⊗ B))
□-φ _ (a , b) = λ n → (a n , b n)

-- Next, we give the counit and comultiplication of the
-- comonad. The ε natural transformation (pronounced
-- "extract") is the counit, and permits "extracting" an A
-- from a □A.  The δ natural transformation is pronounced
-- "duplicate". (These pronunciations come from linear logic,
-- IIRC.)

ε : {A : Obj} → Hom (□ A , A)
ε n box = box n

δ : {A : Obj} → Hom (□ A , □ (□ A))
δ n box = λ n → box

-- We also need to express the special structure relating
-- later and always. The move natural transormation
-- essentially says that if we always have A, then we always
-- have A tomorrow as well.

move : {A : Obj} → Hom (□ A , • (□ A))
move zero boxa = tt
move (suc n) boxa = boxa

-- We can also define fixed points. This is defined by
-- induction on the time index, and the extra parameters
-- (the □Γ) have to be box'd because it has to b used at
-- many different times. 

fix : {Γ B : Obj} → Hom ((□ Γ ⊗ • B), B) → Hom(□ Γ , B)
fix f zero γ    = f 0 (γ , tt)
fix f (suc n) γ = f (suc n) (γ , fix f n γ)

-- To show that this interprets the syntax, we have to define
-- the syntax! First, we give a datatype for the syntax of
-- types.

data type : Set where
  One  : type
  _*_  : type → type → type
  _=>_ : type → type → type
  Box  : type → type
  Next : type → type

-- We also give a datatype for the time qualifiers.

data time : Set where
  Now : time
  Always : time
  Later : time

-- We'll represent contexts as lists of types and times. We'll
-- leave off variable names, and simply index into terms via
-- numeric positions de Bruijn style.

context = List (type × time)

-- This is just a minor bit of notation to make writing
-- contexts prettier.

pattern _,_at_ Γ A q = (A , q) ∷ Γ

-- We also need to define the context modification operations

-- The later function drops all Now hypotheses and changes
-- Later hypotheses to Now, effectively advancing time.

later : context → context
later [] = []
later (Γ , A at Now)    = later Γ
later (Γ , A at Later)  = (later Γ) , A at Now
later (Γ , A at Always) = (later Γ) , A at Always 

-- The always function keeps only the Always hypotheses.

always : context → context
always [] = []
always (Γ , A at Now)    = always Γ
always (Γ , A at Later)  = always Γ
always (Γ , A at Always) = (always Γ) , A at Always 


-- We now give a datatype of well-typed terms. You could also
-- view this as a datatype of typing derivations; the
-- difference is somewhat in the eye of the beholder!

-- First, we define variables as indices into a context, which
-- also say what the type and time they index is.

data variable : context → type → time → Set where
   var-z : {Γ : context} {A : type} {q : time} → 
           --------------------------
           variable (Γ , A at q) A q

   var-s : {Γ : context}{A B : type}{q q' : time }{n : ℕ} → 

           variable Γ A q →
           ---------------------------
           variable (Γ , B at q') A q
   

data term : context → type → time → Set where

   -- The first set of operations correspond to the variable
   -- rule.  We have two variable rules, one permitting Now
   -- variables, and one permitting Always variables.

   var-now : {Γ : context} {A : type} → 

             variable Γ A Now →
             ---------------------------------
             term Γ A Now

   var-always : {Γ : context} {A : type} → 

                variable Γ A Always →
                ---------------------------------
                term Γ A Now

   -- The introduction term for units.

   unit : {Γ : context} → 
          ----------------------------
          term Γ One Now

   -- We can also form and deconstruct pairs. 

   pair : {Γ : context} {A B : type} → 

          term Γ A Now → 
          term Γ B Now → 
          -------------------------
          term Γ (A * B) Now

   pi-1  : {Γ : context} {A B : type} → 

           term Γ (A * B) Now → 
           --------------------------
           term Γ A Now 

   pi-2  : {Γ : context} {A B : type} → 

           term Γ (A * B) Now → 
           ---------------------------
           term Γ B Now

   -- Functions are introduced with lambda-abstraction and
   -- eliminated with application.

   lam : {Γ : context} {A B : type} → 

         term (Γ , A at Now) B Now → 
         --------------------------------
         term Γ (A => B) Now

   app : {Γ : context} {A B : type} → 

         term Γ (A => B) Now → 
         term Γ A Now → 
         ---------------------------
         term Γ B Now
 
   -- The next introduction form checks its premise in a later
   -- context, and the let-next form introduces a Later
   -- hypothesis.

   next : {Γ : context} {A : type} → 

          term (later Γ) A Now → 
          ----------------------------
          term Γ (Next A) Now


   let-next : {Γ : context} {A C : type} →

              term Γ (Next A) Now →
              term (Γ , A at Later) C Now →
              ------------------------------------
              term Γ C Now

   -- The box introduction form checks its premise in an
   -- always context, and the let-next form introduces an
   -- always hypothesis.

   box : {Γ : context} {A : type} → 

         term (always Γ) A Now → 
         ----------------------------------
         term Γ A Always

   let-box : {Γ : context} {A C : type} →

             term Γ (Box A) Now →
             term (Γ , A at Always) C Now →
             -----------------------------------
             term Γ C Now

   -- The recursor only permits capturing always hypotheses,
   -- but lets you use A later as well.

   rec : {Γ : context} {A : type} → 

         term (always Γ , A at Later) A Now → 
         -------------------------------------------
         term Γ A Now 

-- Now we'll give the denotational semantics.
--
-- The general pattern of categorical semantics is that we
-- interpret types as the objects of a category, and the
-- terms get interpreted as morphisms. 

-- So first, we'll give the interpretation of types. This is
-- an infix definition, mapping each syntactic type to an
-- object of Set^ℕ using the constructions we defined above.

[_]-type : type → Obj
[ One ]-type     = I
[ t * t' ]-type  = [ t ]-type ⊗ [ t' ]-type
[ t => t' ]-type = [ t ]-type ⇒ [ t' ]-type
[ Box t ]-type   = □ [ t ]-type
[ Next t ]-type  = • [ t ]-type
  
-- Because we have time qualifiers, we'll also say how to
-- interpret a type paired with a time. 

[_]-hyp : type × time → Obj
[ A , Now ]-hyp    = [ A ]-type
[ A , Always ]-hyp = □ [ A ]-type
[ A , Later ]-hyp  = • [ A ]-type

-- A context is interpreted as a nested tuple of types. 

[_]-ctx : context → Obj
[ [] ]-ctx         = I
[ Γ , A at q ]-ctx = [ Γ ]-ctx ⊗ [ A , q ]-hyp 

-- The later-ctx function shows there is a map from the
-- interpretation of a context to the interpretation of a
-- later context. We drop the now hypotheses, and make use of
-- the monoidal structure of the •A functor to to turn a
-- collection of later hypotheses into a single later nested
-- tuple.

later-ctx : (Γ : context) → Hom([ Γ ]-ctx , • [ later Γ ]-ctx)
later-ctx []                = •-ε
later-ctx (Γ , A at Now)    = fst · later-ctx Γ
later-ctx (Γ , A at Later)  = (later-ctx Γ  ⊗' id) · •-φ
later-ctx (Γ , A at Always) = (later-ctx Γ ⊗' move) · •-φ

-- The always-ctx function shows there is a map from the
-- interpretation of a context to the interpretation of an
-- always context. We drop the now and later hypotheses, and
-- make use of the monoidal structure of the □A functor to to
-- turn a collection of always hypotheses into a single always
-- nested tuple.

always-ctx : (Γ : context) → 
             Hom([ Γ ]-ctx , □ [ always Γ ]-ctx)
always-ctx []                = □-ε
always-ctx (Γ , A at Now)    = fst · always-ctx Γ
always-ctx (Γ , A at Later)  = fst · always-ctx Γ
always-ctx (Γ , A at Always) = (always-ctx Γ ⊗' δ) · □-φ


-- Finally, we can give the interpretation of the syntax.

-- First, we give an interpretation of variables. Because the
-- context is a nested tuple, access into the n-th position in
-- the contest consists of projecting away the n-1 leading
-- components with fst, and the projecting out the right
-- component with snd.

sem-variable : {Γ : context} {A : type} {q : time} → 
               variable Γ A q → Hom([ Γ ]-ctx , [ A , q ]-hyp)
sem-variable var-z     = snd 
sem-variable (var-s x) = fst · sem-variable x

-- We use variable intepretation as a subroutine to interpret
-- the syntax. Because of the close connection between each
-- type and its semantics, the interpretation essentially just
-- does some combinator plumbing to get variables to where
-- they are needed.

sem : {Γ : context} {A : type} {q : time} → 
      term Γ A q →
      Hom([ Γ ]-ctx , [ A , q ]-hyp)

sem     (var-now x)     = sem-variable x 
sem     (var-always x)  = sem-variable x · ε
sem     unit            = ∗
sem     (pair t t')     = < sem t , sem t' >
sem     (pi-1 tm)       = sem tm · fst
sem     (pi-2 tm)       = sem tm · snd
sem     (lam tm)        = curry (sem tm)
sem     (app t t')      = < id , sem t' > · uncurry (sem t)
sem {Γ} (next tm)       = later-ctx Γ · •' (sem tm)
sem     (let-next t t') = < id , sem t > · sem t'
sem {Γ} (box tm)        = always-ctx Γ · □' (sem tm)
sem     (let-box t t')  = < id , sem t > · sem t'
sem {Γ} (rec t)         = always-ctx Γ · fix (ε ⊗' id · sem t)


-- Proofs

postulate extensionality : {A : Set} {B : A → Set} (f g : (a : A) → B a) → ((a : A) → f a ≡ g a) → f ≡ g 
postulate extensionality-2 : {A : Set} {B : A → Set} {C : (a : A) → B a → Set}
                             {f g : (a : A) → (b : B a) → C a b} → 
                             ((a : A) → (b : B a) → f a b ≡ g a b) → f ≡ g 

-- Properties of the terminal object

I-η : {A : Obj} → (f : Hom (A , I)) → f ≡ ∗
I-η f = extensionality-2 (λ a b → refl)


-- Properties of products A ⊗ B 

⊗-β₁ : {A B C : Obj} → (f : Hom (A , B)) (g : Hom (A , C)) →
             (< f , g > · fst) ≡ f 
⊗-β₁ f g = refl

⊗-β₂ : {A B C : Obj} → (f : Hom (A , B)) (g : Hom (A , C)) →
             (< f , g > · snd) ≡ g
⊗-β₂ f g = refl

⊗-η : {A B C : Obj} → (f : Hom (A , (B ⊗ C))) →
             (< f · fst , f · snd >) ≡ f
⊗-η {A} {B} {C} f = extensionality-2 (λ n a → refl) 

⊗'-id : {A B : Obj} → (id {A}) ⊗' (id {B}) ≡ id
⊗'-id {A} {B} = refl

⊗'-· : {A B C X Y Z : Obj} → (f : Hom(A , B)) → (f' : Hom(B , C))
                            → (g : Hom(X , Y)) → (g' : Hom(Y , Z))
        → ((f · f') ⊗' (g · g')) ≡ ((f ⊗' g) · (f' ⊗' g'))
⊗'-· f f' g g' = refl

-- Properties of A ⇒ B

uncurry-curry : {A B C : Obj} → (f : Hom((A ⊗ B) , C)) →
                  uncurry (curry f) ≡ f
uncurry-curry f = extensionality-2 (λ a b → refl)

curry-uncurry : {A B C : Obj} → (f : Hom(A  , B ⇒ C)) →
                  curry (uncurry f) ≡ f
curry-uncurry f = extensionality-2 (λ a b → refl)

⇒'-id : {A B : Obj} → (f : Hom (A , B)) → ((id {A}) ⇒' (id {B})) ≡ id 
⇒'-id f = refl

⇒'-· : {A B C X Y Z : Obj} 
        → (f : Hom (A , B)) → (f' : Hom(B , C))
        → (g : Hom (X , Y)) → (g' : Hom(Y , Z))
        → ((f · f') ⇒' (g · g')) ≡ ((f' ⇒' g) · (f ⇒' g'))
⇒'-· f f' g g' = refl        

-- Properties of • A

•'-id : {A : Obj} → •' (id {A}) ≡ id {• A}
•'-id {A} = extensionality-2 H where
  H : (n : ℕ) (a' : • A n) → •' id n a' ≡ a'
  H zero a' = refl
  H (suc n) a' = refl

•'-· : {A B C : Obj} → (f : Hom(A , B)) → (g : Hom(B , C)) 
       → (•' (f · g)) ≡ ((•' f) · (•' g))
•'-· {A} f g = extensionality-2 H where
  H : (n : ℕ) (a : • A n) →
        •' (λ n a → g n (f n a)) n a ≡ •' g n (•' f n a)
  H zero a = refl
  H (suc n) a = refl

•-ε-iso₁ : (•-ε · •-ε') ≡ id
•-ε-iso₁ = refl

•-ε-iso₂ : (•-ε' · •-ε) ≡ id
•-ε-iso₂ = extensionality-2 H where
  H : (n : ℕ) (f : • (λ _ → ⊤) n) → •-ε n tt ≡ f
  H zero tt = refl
  H (suc n) tt = refl

•-φ-iso₁ : {A B : Obj} → (•-φ · •-φ') ≡ (id {• A ⊗ • B})
•-φ-iso₁ {A} {B} = extensionality-2 H where
  H : (n : ℕ) (v : • A n × • B n) → •-φ' n (•-φ n v) ≡ v
  H zero v = refl
  H (suc n) v = refl

•-φ-iso₂ : {A B : Obj} → (•-φ' · •-φ) ≡ (id {• (A ⊗ B)})
•-φ-iso₂ {A} {B} = extensionality-2 H where
  H : (n : ℕ) (v : • (λ z → A z × B z) n) → •-φ n (•-φ' n v) ≡ v
  H zero v = refl
  H (suc n) v = refl

-- Properties of adjunctions

adj-iso₁ : {A : Obj} {X : Set} → (f : Hom(F X , A)) → adj' (adj f) ≡ f
adj-iso₁ f = refl

adj-iso₂ : {A : Obj} {X : Set} → (f : X → G A) → adj (adj' f) ≡ f
adj-iso₂ f = refl
