\documentclass{report}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{fontspec}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb F}}}
\newunicodechar{𝕃}{\ensuremath{\mathnormal{\mathbb L}}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{𝕊}{\ensuremath{\mathnormal{\mathbb S}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal{\mathbb Z}}}
\newunicodechar{ℚ}{\ensuremath{\mathnormal{\mathbb Q}}}
\newunicodechar{∘}{\ensuremath{\mathnormal\circ}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{⊤}{\ensuremath{\mathnormal\top}}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{→}{\ensuremath{\mathnormal\rightarrow}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{∉}{\ensuremath{\mathnormal\notin}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\hspace{-0.3em}|}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{|\hspace{-0.3em}\rbrace}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_\AgdaFontStyle{i}}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_\AgdaFontStyle{l}}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_\AgdaFontStyle{s}}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_\AgdaFontStyle{v}}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_\AgdaFontStyle{o}}}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{ʳ}{\ensuremath{\mathnormal{^\AgdaFontStyle{r}}}}
\newunicodechar{ᵘ}{\ensuremath{\mathnormal{^\AgdaFontStyle{u}}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal\uplus}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{≗}{\ensuremath{\mathnormal\circeq}}
\newunicodechar{∧}{\ensuremath{\mathnormal\land}}
\newunicodechar{≤}{\ensuremath{\mathnormal\leq}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_m}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{∸}{\ensuremath{\mathnormal\divdot}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{𝓁}{\ensuremath{\mathnormal{\mathcal l}}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal\ell}}
\newunicodechar{χ}{\ensuremath{\mathnormal\chi}}
\newunicodechar{⊃}{\ensuremath{\mathnormal\supset}}
\newunicodechar{▹}{\ensuremath{\mathnormal\triangleright}}
\newunicodechar{⊔}{\ensuremath{\mathnormal\sqcup}}
\newunicodechar{⊓}{\ensuremath{\mathnormal\sqcap}}
\newunicodechar{⟲}{\ensuremath{\mathnormal\circlearrowleft}}
\newunicodechar{𝓫}{\ensuremath{\mathnormal{\mathcal b}}}
\newunicodechar{𝓰}{\ensuremath{\mathnormal{\mathcal g}}}
\newunicodechar{𝓵}{\ensuremath{\mathnormal{\mathcal l}}}

\newfontface{\ayyplcihartai}{APL333}
\DeclareTextFontCommand{\ayypl}{\ayyplcihartai}
\newunicodechar{⌽}{\ensuremath{\ayypl ⌽}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\IC\AgdaInductiveConstructor
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\newcommand\Xr[2]{\textrm{#1(#2)}}

\title{le me'oi .Agda.\ velcki be la'o zoi.\ \Xr{shat}{1} .zoi.\ noi ke'a smimlu la'o zoi.\ \Xr{ed}{1} .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\begin{abstract}
ni'o skicu bau la'oi .Agda.\ fe ko'a goi le milxe be le ka ce'u smimlu be la'o zoi.\ \Xr{ed}{1}\ .zoi.\ pe la'o zoi.\ Version 1 AT\&T UNIX\ .zoi.\ldots kei be'o poi ke'a selcme zoi zoi.\ \Xr{shat}{1}\ .zoi.\ldots ku'o je cu ciksi bau la'oi .Agda.\ le ctaipe be le su'u ko'a co'e ja mapti
\end{abstract}

\tableofcontents

\chapter{le vrici}

\begin{code}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --overlapping-instances #-}
{-# OPTIONS --instance-search-depth=2 #-}

open import IO
  using (
    Main;
    run;
    IO
  )
open import Data.Fin
  as 𝔽
  using (
    Fin
  )
open import Data.Nat
  as ℕ
  using (
    ℕ
  )
open import Data.Sum
  using (
    from-inj₁;
    map₁;
    inj₂;
    inj₁;
    _⊎_
  )
open import Function
  using (
    typeOf;
    _on_;
    _∘₂_;
    flip;
    _∋_;
    _$_;
    _∘_;
    id
  )
  renaming (
    _|>_ to _▹_
  )
open import IO.Finite
  using (
    readFile
  )
open import Data.Bool
  using (
    false;
    T?
  )
  renaming (
    if_then_else_ to if
  )
open import Data.Char
  using (
    isDigit;
    Char
  )
open import Data.List
  as 𝕃
  using (
    List;
    _∷_;
    []
  )
  renaming (
    lookup to _!_;
    drop to _↓_;
    take to _↑_
  )
open import Data.Maybe
  using (
    decToMaybe;
    from-just;
    nothing;
    Maybe;
    maybe;
    just
  )
open import Data.String
  as 𝕊
  using (
    unlines;
    String;
    lines
  )
open import Data.Product
  using (
    uncurry;
    proj₂;
    proj₁;
    _×_;
    _,_;
    ∃;
    Σ
  )
open import Relation.Unary
  using (
    Decidable;
    Pred
  )
open import Relation.Nullary
  using (
    Dec;
    yes;
    ¬_;
    no
  )
open import System.Environment
  using (
    getArgs
  )
open import Truthbrary.Data.Fin
  using (
    mink
  )
open import Truthbrary.Record.Eq
  using (
    _≡ᵇ_;
    _≟_
  )
open import Truthbrary.Record.SR
  using (
    readMaybe;
    Show;
    show
  )
open import Data.Unit.Polymorphic
  using (
    ⊤
  )
open import Truthbrary.Record.LLC
  using (
    liliList;
    length;
    _++_;
    _∉_;
    cev;
    vec
  )
open import Truthbrary.Category.Monad
  using (
    _<=<_;
    _=<<_;
    _>>=_
  )
  renaming (
    map to mapₘ
  )
open import Truthbrary.Data.List.Split
  using (
    splitOn
  )
open import Relation.Binary.PropositionalEquality
  using (
    module ≡-Reasoning;
    cong;
    refl;
    _≗_;
    _≡_;
    sym
  )

import Data.Fin.Show
  as 𝔽
import Agda.Builtin.IO
  as ABIO
import Agda.Builtin.Unit
  as ABU
import Data.Fin.Properties
  as DFP
import Data.Nat.Properties
  as DNP
import Data.List.Properties
  as DLP
import Data.Maybe.Instances
import Data.Maybe.Properties
  as DMP
import Relation.Nullary.Decidable
import Data.List.Relation.Unary.All
  as 𝕃
  using (
    All
  )
\end{code}

\chapter{le me'oi .instance.\ pe le na se ciksi fo le velcki be le la'o zoi.\ \Xr{shat}{1}\ .zoi.}

\begin{code}
showF : {n : ℕ} → Show $ Fin n
showF = record {show = 𝔽.show}
\end{code}

\chapter{le se ctaipe}

\section{la'oi .\AgdaRecord{Buffer}.}
ni'o ciksi la'oi .\AgdaRecord{Buffer}.\ fo ma poi ke'a zabna ku'o bau la .lojban.

\begin{code}
record Buffer : Set
  where
  field
    datnyveicme : Maybe String
    lerpinste : List String
    cablerpinsle : Fin $ length lerpinste
    citri : List $ Σ (typeOf lerpinste) $ Fin ∘ length
    rejgaudatni : Maybe String
  F = typeOf cablerpinsle
  cninycitri = (lerpinste , cablerpinsle) ∷ citri
\end{code}

\subsection{tu'a la'oi .\D{Fin}.}
ni'o tu'a la'oi .\D{Fin}.\ nibli ko'a goi le su'u ro da poi ke'a ctaipe la'oi .\AgdaRecord{Buffer}.\ zo'u li su'o co'e ja nilzilcmi lo mu'oi zoi.\ \AgdaField{Buffer.lerpinste}\ .zoi.\ be da  .i pilno le co'e co ke na'e me mu'oi zoi.\ \F{if\AgdaUnderscore{}then\AgdaUnderscore{}else\AgdaUnderscore} .zoi.\ ki'u le su'u ko'a milxe ko'e goi le ka ce'u fegli la .varik.\ldots kei je ku'i cu mleca fi ko'e je le ka tu'a ce'u frili kei fe lo jalge be lo nu la'o zoi.\ \AgdaField{Buffer.cablerpinsle} .zoi.\ ctaipe la'o zoi.\ \Sym(\B x \Sym : \AgdaRecord{Buffer}\Sym) \Sym → \F{if} \Sym(\AgdaNumber 0 \OpF{ℕ.≤} \F{length} \Sym(\AgdaField{Buffer.lerpinste} \B x\Sym)\Sym) \Sym(\AgdaField{Buffer.F} \B x\Sym) \D ⊤\ .zoi.

\section{la'oi .\D{Cmd}.}
ni'o ctaipe ko'a goi la'o zoi.\ \D{Cmd} \B x\ .zoi.\ fa lo co'e be lo midnoi be fo la'o zoi.\ \Xr{ed}{1} .zoi.\ ja zo'e be'o poi ctaipe lo su'u tu'a ke'a racli

\newcommand\pavysumti[2]{ga je da du la'o zoi.\ \IC{#1} \B v\ .zoi.\ gi da mapti lo konkatena be lo sinxa be la'oi .\B v.\ be'o bei #2}
\newcommand\cibysumti[2]{ga je da du la'o zoi.\ \IC{#1} \B v \B z \AgdaUnderscore{}\ .zoi.\ gi da mapti lo konkatena be lo sinxa be la'oi .\B v.\ be'o bei lo me'oi .comma.\ bei lo sinxa be la'oi .\B z.\ be'o bei #2}
\newcommand\vonsumti[2]{ga je da du la'o zoi.\ \IC{#1} \B v \B x \B z\ \AgdaUnderscore{}\ .zoi.\ gi da mapti lo konkatena be lo sinxa be la'oi .\B v.\ be'o bei lo me'oi .comma.\ bei lo sinxa be la'oi .\B x.\ be'o bei #2\ bei lo sinxa be la'oi .\B z.}
.i ro da poi ke'a ctaipe ko'a zo'u\ldots
\begin{itemize}
	\item ga jonai ga je da du la'oi .\IC{Sisti}.\ gi da mapti zo'oi .q.\ gi
	\item ga jonai ga je da du la'oi .\IC{Sisti!}.\ gi da mapti zo'oi .Q.\ gi
	\item ga jonai ga je da du la'o zoi.\ \IC{Xruti}\ \B z.\ .zoi.\ gi da mapti zo'oi .u.\ldots je ku'i cu mapti le meirmoi be la'oi .\B z.\ bei fo la'o zoi.\ \AgdaField{Buffer.citri} \B x\ .zoi.\ gi
	\item ga jonai \pavysumti{Jmina}{zo'oi .a.}\ gi
	\item ga jonai \pavysumti{Jmini}{zo'oi .i.}\ gi
	\item ga jonai ga je da du la'o zoi.\ \IC{Rejgau} \B v\ .zoi.\ gi da mapti lo konkatena be zo'oi .w.\ bei lo canlu lerfu bei la'oi .\B v.\ gi
	\item ga jonai \cibysumti{Vimcu}{zo'oi .d.} gi
	\item ga jonai \cibysumti{Muvgau}{zo'oi .m.} gi
	\item ga jonai \cibysumti{Cusku}{zo'oi .p.} gi
	\item ga jonai \cibysumti{Namcusku}{zo'oi .n.} gi
	\item \vonsumti{Basti}{zo'oi .c.}
\end{itemize}

\begin{code}
data Cmd (x : Buffer) : Set where
  Sisti : Cmd x
  Sisti! : Cmd x
  Jmina : Buffer.F x → Cmd x
  -- | ni'o la .varik. cu cnikansa lo se rigni
  -- be le klamburi
  Jmini : Buffer.F x → Cmd x
  Rejgau : String → Cmd x
  Vimcu : (a b : Buffer.F x) → a 𝔽.≤ b → Cmd x
  Namcusku : typeOf Vimcu
  Basti : typeOf Vimcu
  Cusku : typeOf Vimcu
  Muvgau : (a b c : Buffer.F x) → a 𝔽.≤ b → Cmd x
  Xruti : Fin $ length $ Buffer.citri x → Cmd x
\end{code}

\section{la'oi .\D{Cmdᵢₒ}.}
ni'o ro da poi ke'a ctaipe la'o zoi.\ \D{Cmdᵢₒ} \B x\ .zoi.\ zo'u\ldots
\begin{itemize}
	\item ga jonai ga je da du la'o zoi.\ \IC{Rejgauᵢₒ} \B a \B b\ .zoi.\ gi tu'a da rinka lo nu rejgau benji la'oi .\B a.\ lo datnyvei poi ke'a selcme la'oi .\B b.\ gi
	\item ga jonai ga je da du la'o zoi.\ \IC{Tciduᵢₒ} \B a \B b\ .zoi.\ gi tu'a da rinka tu'a lo ctaipe be la'oi .\AgdaRecord{Buffer}.\ poi ro de poi ke'a xi pa ctaipe lo me'oi .\F{BufF}.\ be ke'a xi re zo'u ga jonai lo meirmoi be de bei fo ko'e goi lo mu'oi zoi.\ \AgdaField{Buffer.lerpinste}\ .zoi.\ be ke'a cu meirmoi de fo ko'a goi la'o zoi.\ \AgdaField{Buffer.lerpinste} \B x\ .zoi.\ gi ga jonai ga je de zmadu la'oi .\B b.\ je cu dubjavme'a ko'i goi lo nilzilcmi be ko'o goi lo'i ro lerpinsle be lo datnyvei poi ke'a xi re selcme la'oi .\B b.\ gi lo meirmoi be da bei fo ko'e cu meirmoi be lo vujnu be da bei ko'i fo ko'o gi ga je da zmadu la'oi .\B b.\ jenai cu dubjavme'a ko'i gi lo meirmoi be da bei fo ko'e cu meirmoi lo vujnu be da bei la'oi .\B b.\ fo ko'a gi
	\item ga jonai ga je da du la'oi .\IC{Sistiᵢₒ}.\ gi tu'a da rinka lo nu co'e ja kajde ja cu sisti tu'a la'o zoi.\ \Xr{shat}{1}\ .zoi.\ gi
	\item ga jonai ga je da du la'oi .\IC{Sisti!ᵢₒ}.\ gi tu'a da rinka lo nu sisti tu'a la'o zoi.\ \Xr{shat}{1}\ .zoi.\ gi
	\item ga je da du la'o zoi.\ \IC{Skamiᵢₒ} \B x\ .zoi.\ gi tu'a da rinka lo nu .uniks.\ co'e la'oi .\B x.
\end{itemize}

\begin{code}
data Cmdᵢₒ (x : Buffer) : Set where
  Rejgauᵢₒ : String → String → Cmdᵢₒ x
  Tciduᵢₒ : String → Buffer.F x → Cmdᵢₒ x
  Skamiᵢₒ : String → Cmdᵢₒ x
  Sistiᵢₒ : Cmdᵢₒ x
  Sisti!ᵢₒ : Cmdᵢₒ x
\end{code}

\chapter{le fancu}

\section{la'oi .\F{insert}.}
ni'o la .varik.\ na birti lo du'u ma kau zabna je cu lojbo je cu velcki la'oi .\F{insert}.  .i la .varik.\ cu stidi lo nu lo na jimpe cu tcidu le velcki be le ctaipe be le su'u la'oi .\F{insert}.\ mapti

\begin{code}
insert : ∀ {a} → {A : Set a}
       → (x i : List A)
       → Maybe $ Fin $ length x
       → List A
insert x i nothing = x ++ i
insert x i (just n) = (n' ↑ x) ++ i ++ (n' ↓ x)
  where
  n' = 𝔽.toℕ n
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{insert}.\ mapti}

\begin{code}
module InsertVeritas where
  private
    lendrop : ∀ {a} → {A : Set a}
            → (x z : List A)
            → z ≡_ $ length x ↓_ $ x ++ z
    lendrop [] _ = refl
    lendrop (_ ∷ xs) z = lendrop xs z

    lenteik : ∀ {a} → {A : Set a}
            → (x z : List A)
            → x ≡_ $ length x ↑_ $ x ++ z
    lenteik [] _ = refl
    lenteik (x ∷ xs) z = lenteik xs z ▹ cong (x ∷_)

    finlen : ∀ {a} → {A : Set a}
           → (xs : List A)
           → (n : Fin $ length xs)
           → 𝔽.toℕ n ≡ length (𝔽.toℕ n ↑ xs)
    finlen (_ ∷ _) 𝔽.zero = refl
    finlen (_ ∷ xs) (𝔽.suc n) = finlen xs n ▹ cong ℕ.suc
       
  lynyrd : ∀ {a} → {A : Set a}
         → (x i : List A)
         → (n : Maybe $ Fin $ length x)
         → length x ℕ.+ length i ≡ length (insert x i n)
  lynyrd x i nothing = DLP.length-++ x ▹ sym
  lynyrd x i (just n) = sym $ begin
    L (insert x i $ just n)
      ≡⟨ refl ⟩
    L ((n' ↑ x) ++ i ++ (n' ↓ x))
      ≡⟨ DLP.length-++ $ n' ↑ x ⟩
    L (n' ↑ x) ℕ.+ L (i ++ (n' ↓ x))
      ≡⟨ DLP.length-++ i ▹ cong (ℕ._+_ _) ⟩
    L (n' ↑ x) ℕ.+ (L i ℕ.+ L (n' ↓ x))
      ≡⟨ DNP.+-comm (L i) _ ▹ cong (ℕ._+_ $ L $ n' ↑ x) ⟩
    L (n' ↑ x) ℕ.+ (L (n' ↓ x) ℕ.+ L i)
      ≡⟨ DNP.+-assoc (L $ n' ↑ x) _ _ ▹ sym ⟩
    L (n' ↑ x) ℕ.+ L (n' ↓ x) ℕ.+ L i
      ≡⟨ DLP.length-++ (n' ↑ x) ▹ sym ▹ cong (ℕ._+ L i) ⟩
    L (n' ↑ x ++ n' ↓ x) ℕ.+ L i
      ≡⟨ DLP.take++drop n' x ▹ cong ((ℕ._+ L i) ∘ L) ⟩
    L x ℕ.+ L i ∎
    where
    L = length
    n' = 𝔽.toℕ n
    open ≡-Reasoning

  pamois : ∀ {a} → {A : Set a}
         → (x i : List A)
         → (n : Maybe $ Fin $ length x)
         → let n' = maybe 𝔽.toℕ (length x) n in
           ((_≡_ on (_↑_ n'))
             x
             (insert x i n))
  pamois = {!!}

  remois : ∀ {a} → {A : Set a}
         → (x i : List A)
         → (n : Maybe $ Fin $ length x)
         → let n' = maybe 𝔽.toℕ (length x) n in
           i ≡_ $ length i ↑_ $ n' ↓ insert x i n
  remois x i nothing = sym $ begin
    L i ↑ (L x ↓ insert x i nothing) ≡⟨ refl ⟩
    L i ↑ (L x ↓_ $ x ++ i) ≡⟨ lendrop x i ▹ sym ▹ cong (_ ↑_) ⟩
    L i ↑ i ≡⟨ DLP.++-identityʳ i ▹ sym ▹ cong (L i ↑_) ⟩
    L i ↑ (i ++ []) ≡⟨ lenteik i [] ▹ sym ⟩
    i ∎
    where
    L = length
    open ≡-Reasoning
  remois x i (just n) = sym $ begin
    L i ↑ (n' ↓ insert x i (just n)) ≡⟨ refl ⟩
    L i ↑ (n' ↓_ $ x₁ ++ i ++ x₂) ≡⟨ refl ⟩
    _ ≡⟨ finlen x n ▹ cong (L i ↑_ ∘ flip _↓_ (x₁ ++ i ++ x₂)) ⟩
    L i ↑ (L x₁ ↓_ $ x₁ ++ i ++ x₂) ≡⟨ refl ⟩
    _ ≡⟨ lendrop x₁ _ ▹ sym ▹ cong (_ ↑_) ⟩
    L i ↑ (i ++ x₂) ≡⟨ lenteik i x₂ ▹ sym ⟩
    i ∎
    where
    L = length
    n' = 𝔽.toℕ n
    x₁ = n' ↑ x
    x₂ = n' ↓ x
    open ≡-Reasoning

  romois : ∀ {a} → {A : Set a}
         → (x i : List A)
         → (n : Maybe $ Fin $ length x)
         → let n' = maybe 𝔽.toℕ (length x) n in
           n' ↓ x ≡ (n' ℕ.+ length i) ↓ insert x i n
  romois = {!!}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{},ₘ\AgdaUnderscore}\ .zoi.}
ni'o xu sarcu fa lo nu ciksi bau la .lojban.

\begin{code}
_,ₘ_ : ∀ {a} → {A B : Set a}
     → Maybe A → Maybe B → Maybe $ A × B
_,ₘ_ = Data.Maybe.ap ∘₂ mapₘ $ _,_
\end{code}

\section{la'o zoi.\ \F{dec-just}\ .zoi.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi fo lo lojbo fe la'o zoi.\ \F{dec-just}\ .zoi.

\begin{code}
dec-just : ∀ {a p} → {A : Set a}
         → {P : Pred A p}
         → {x : A}
         → {P? : Dec $ P x}
         → (m : P x)
         → ∃ $ λ m → decToMaybe P? ≡ just m
dec-just {P? = P?} m = Data.Product.dmap id (cong decToMaybe) M
  where
  M = Relation.Nullary.Decidable.dec-yes P? m
\end{code}

\section{la'o zoi.\ \F{dec-nothing}\ .zoi.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi fo lo lojbo fe la'o zoi.\ \F{dec-nothing}\ .zoi.

\begin{code}
dec-nothing : ∀ {a p} → {A : Set a}
            → {P : Pred A p}
            → {x : A}
            → {P? : Dec $ P x}
            → (m : ¬ P x)
            → decToMaybe P? ≡ nothing
dec-nothing {P? = P?} m = begin
  decToMaybe P? ≡⟨ M ▹ proj₂ ▹ cong decToMaybe ⟩
  decToMaybe (no $ proj₁ M) ≡⟨ refl ⟩
  nothing ∎
  where
  M = Relation.Nullary.Decidable.dec-no P? m
  open ≡-Reasoning
\end{code}

\section{la \F{dekydu'i}}
ni'o xu sarcu fa lo nu la .varik.\ cu ciksi la \F{dekydu'i} bau la .lojban.

\begin{code}
dekydu'i : {x n : ℕ}
         → {m : x ℕ.< n}
         → decToMaybe (x ℕ.<? n) ≡ just m
dekydu'i {x} {n} {m} = begin
  decToMaybe (x ℕ.<? n) ≡⟨ DY ▹ proj₂ ▹ cong decToMaybe ⟩
  decToMaybe (yes $ proj₁ DY) ≡⟨ refl ⟩
  _ ≡⟨ iedek (proj₁ DY) m ▹ cong (decToMaybe ∘ yes) ⟩
  decToMaybe (yes m) ≡⟨ refl ⟩
  just m ∎
  where
  DY = Relation.Nullary.Decidable.dec-yes (x ℕ.<? n) m
  iedek : {m n : ℕ} → (x z : m ℕ.< n) → x ≡ z
  iedek (ℕ.s≤s ℕ.z≤n) (ℕ.s≤s ℕ.z≤n) = refl
  iedek {ℕ.suc m} {ℕ.suc n} (ℕ.s≤s x) (ℕ.s≤s z) = I
    where
    I = iedek {m} {n} x z ▹ cong ℕ.s≤s
  open ≡-Reasoning
\end{code}

\section{la \F{zmadekydu'i}}

\begin{code}
zmadekydu'i : {x n : ℕ}
            → {m : x ℕ.≤ n}
            → decToMaybe (x ℕ.≤? n) ≡ just m
zmadekydu'i {x} {n} {m} = begin
  decToMaybe (x ℕ.≤? n) ≡⟨ DY ▹ proj₂ ▹ cong decToMaybe ⟩
  decToMaybe (yes $ proj₁ DY) ≡⟨ refl ⟩
  _ ≡⟨ iedek (proj₁ DY) m ▹ cong (decToMaybe ∘ yes) ⟩
  decToMaybe (yes m) ≡⟨ refl ⟩
  just m ∎
  where
  DY = Relation.Nullary.Decidable.dec-yes (x ℕ.≤? n) m
  iedek : {m n : ℕ} → (x z : m ℕ.≤ n) → x ≡ z
  iedek ℕ.z≤n ℕ.z≤n = refl
  iedek {ℕ.suc m} {ℕ.suc n} (ℕ.s≤s x) (ℕ.s≤s z) = I
    where
    I = iedek {m} {n} x z ▹ cong ℕ.s≤s
  open ≡-Reasoning
\end{code}

\section{la'oi .\F{fromℕ?}.}
ni'o ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{fromℕ?}\ \B x\ .zoi.\ gi la'o zoi.\ \F{mapₘ} \F{𝔽.toℕ} \OpF \$ \F{fromℕ?}\ \B x\ .zoi.\ me'oi .\IC{just}.\ zo'e poi la'oi .\B x.\ mu'oi zoi.\ \F{𝔽.toℕ}\ .zoi.\ ke'a

\begin{code}
fromℕ? : {n : ℕ} → ℕ → Maybe $ Fin n
fromℕ? = mapₘ 𝔽.fromℕ< ∘ decToMaybe ∘ (ℕ._<? _)
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{fromℕ?}.\ mapti}

\begin{code}
module fromℕ?Veritas where
  pav : {n : ℕ}
      → (x : ℕ)
      → x ℕ.< n
      → just x ≡ mapₘ 𝔽.toℕ (fromℕ? {n} x)
  pav {n} x m = sym $ begin
    mapₘ 𝔽.toℕ (fromℕ? {n} x) ≡⟨ refl ⟩
    mapₘ 𝔽.toℕ (mapₘ 𝔽.fromℕ< $ c? x) ≡⟨ mapmapi $ c? x ⟩
    mapₘ id' (c? x) ≡⟨ dekydu'i ▹ cong (mapₘ id') ⟩
    mapₘ id' (just m) ≡⟨ refl ⟩
    just (id' m) ≡⟨ DFP.toℕ-fromℕ< m ▹ cong just ⟩
    just x ∎
    where
    id' = 𝔽.toℕ ∘ 𝔽.fromℕ<
    c? : (x : ℕ) → Maybe $ x ℕ.< n
    c? = decToMaybe ∘ (ℕ._<? n)
    open ≡-Reasoning
    mapmapi = sym ∘ DMP.map-compose

  rel : {n : ℕ}
      → (x : ℕ)
      → ¬_ $ x ℕ.< n
      → nothing ≡ mapₘ 𝔽.toℕ (fromℕ? {n} x)
  rel {n} x J = sym $ begin
    mapₘ 𝔽.toℕ (fromℕ? {n} x) ≡⟨ refl ⟩
    mapₘ 𝔽.toℕ (mapₘ 𝔽.fromℕ< $ decToMaybe $ x ℕ.<? n) ≡⟨ {!!} ⟩
    mapₘ (𝔽.toℕ ∘ 𝔽.fromℕ<) (decToMaybe $ x ℕ.<? n) ≡⟨ refl ⟩
    _ ≡⟨ DN ▹ proj₂ ▹ cong (mapₘ (𝔽.toℕ ∘ 𝔽.fromℕ<) ∘ decToMaybe) ⟩
    mapₘ (𝔽.toℕ ∘ 𝔽.fromℕ<) (decToMaybe $ no N) ≡⟨ refl ⟩
    nothing ∎
    where
    DN = Relation.Nullary.Decidable.dec-no (x ℕ.<? n) J
    N = ¬ (x ℕ.< n) ∋ proj₁ DN
    open ≡-Reasoning
\end{code}

\section{la'oi .\F{degjygirzu}.}
ni'o la .varik.\ na birti lo du'u ciksi bau la .lojban.\ fe la \F{degjygirzu}\ fo ma kau poi ke'a zabna

\begin{code}
degjygirzu : String → List String
degjygirzu = 𝕊.wordsBy $ T? ∘ Data.Bool.not ∘ isDigit
\end{code}

\subsection{le ctaipe be le su'u la \F{degjygirzu}\ cu mapti}

\begin{code}
module DegjygirzuVeritas where
  pav : ((x : String) → x ≡ 𝕊.fromList (𝕊.toList x))
      → (n : ℕ) → degjygirzu (show n) ≡ show n ∷ []
  pav fL∘tL n = begin
    degjygirzu (show n) ≡⟨ refl ⟩
    𝕃.map 𝕊.fromList (d $ 𝕊.toList $ show n) ≡⟨ refl ⟩
    mL (d $ show' n) ≡⟨ didus n ▹ cong mL ⟩
    mL (show' n ∷ []) ≡⟨ fL∘tL (show n) ▹ sym ▹ cong (_∷ []) ⟩
    show n ∷ [] ∎
    where
    mL = 𝕃.map 𝕊.fromList
    show' = 𝕊.toList ∘ show
    d = 𝕃.wordsBy $ T? ∘ Data.Bool.not ∘ isDigit
    didus : (n : ℕ) → d (show' n) ≡ show' n ∷ []
    didus = {!!}
    open ≡-Reasoning

  rybic : (s : String)
        → (c : Char)
        → false ≡ isDigit c
        → (_≡_
            (degjygirzu s)
            (degjygirzu $ 𝕊.fromChar c ++ s))
  rybic s c j = sym $ begin
    degjygirzu (𝕊.fromChar c ++ s) ≡⟨ refl ⟩
    degjygirzu (fC c ++ s) ≡⟨ refl ⟩
    d' (tL $ fC c ++ s) ≡⟨ tldist (fC c) s ▹ cong d' ⟩
    d' (tL (fC c) ++ tL s) ≡⟨ tilfic c ▹ cong (d' ∘ (_++ tL s)) ⟩
    d' ((c ∷ []) ++ tL s) ≡⟨ refl ⟩
    d' (c ∷ tL s) ≡⟨ refl ⟩
    𝕃.map fL (𝕃.wordsBy (F? ∘ isDigit) $ c ∷ tL s) ≡⟨ refl ⟩
    _ ≡⟨ uobis c (tL s) (fineg j) ▹ cong (𝕃.map fL) ⟩
    𝕃.map fL (𝕃.wordsBy (F? ∘ isDigit) $ tL s) ≡⟨ refl ⟩
    degjygirzu s ∎
    where
    tL = 𝕊.toList
    fL = 𝕊.fromList
    fC = 𝕊.fromChar
    F? = T? ∘ Data.Bool.not
    tldist : (x z : String) → tL (x ++ z) ≡ tL x ++ tL z
    tldist = {!!}
    -- | .i cicna finpe
    tilfic : tL ∘ fC ≗ 𝕃.[_]
    tilfic = {!!}
    d' = 𝕃.map fL ∘_ $ 𝕃.wordsBy $ F? ∘ isDigit
    fineg : {x : Data.Bool.Bool}
          → false ≡ x
          → Data.Bool.T $ Data.Bool.not x
    fineg refl = _
    open ≡-Reasoning
    uobis : ∀ {a p} → {A : Set a}
          → {P : Pred A p}
          → {P? : Decidable P}
          → (x : A)
          → (xs : List A)
          → P x
          → 𝕃.wordsBy P? (x ∷ xs) ≡ 𝕃.wordsBy P? xs
    uobis = {!!}

  rel : (s : String)
      → (t : ℕ)
      → (c : Char)
      → false ≡ isDigit c
      → (_≡_
          (show t ∷ degjygirzu s)
          (degjygirzu $ show t ++ 𝕊.fromChar c ++ s))
  rel s t c j = sym $ begin
    d (show t ++ 𝕊.fromChar c ++ s) ≡⟨ {!!} ⟩
    d (show t) ++ d (𝕊.fromChar c ++ s) ≡⟨ refl ⟩
    _ ≡⟨ rybic s c j ▹ sym ▹ cong (_++_ _) ⟩
    d (show t) ++ d s ≡⟨ pav (sym ∘ fL∘tL) t ▹ cong (_++ d s) ⟩
    (show t ∷ []) ++ d s ≡⟨ refl ⟩
    show t ∷ d s ∎
    where
    d = degjygirzu
    tL = 𝕊.toList
    fL = 𝕊.fromList
    tildist : (x z : String) → tL (x ++ z) ≡ tL x ++ tL z
    tildist = {!!}
    d' = 𝕃.map fL ∘_ $ 𝕃.wordsBy $ T? ∘ Data.Bool.not ∘ isDigit
    fL∘tL = {!!}
    open ≡-Reasoning
\end{code}

\section{la'oi .\F{pamoinamcu}.}
ni'o ro da xi pa poi ke'a na'e degji lerfu zo'u ro da xi re poi ke'a ctaipe la'oi .\AgdaPostulate{String}.\ zo'u ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{pamoinamcu} \B x\ .zoi.\ gi su'o de poi ke'a kacna'u zo'u ga je la'oi .\B x.\ konkatena lo sinxa be de bei de xi pa bei de xi re gi ko'a de me'oi .\IC{just}.

\begin{code}
pamoinamcu : String → Maybe ℕ
pamoinamcu = readMaybe <=< (𝕃.head ∘ degjygirzu)
\end{code}

\subsection{le ctaipe be le su'u mapti fa la'oi .\F{pamoinamcu}.}

\begin{code}
module PamoinamcuVeritas where
  non : ((n : ℕ) → readMaybe (show n) ≡ just n)
      → ((x : String) → x ≡ 𝕊.fromList (𝕊.toList x))
      → (n : ℕ) → just n ≡ pamoinamcu (show n)
  non rimco fL∘tL n = sym $ begin
    pamoinamcu (show n) ≡⟨ refl ⟩
    𝕃.head (s $ show n) >>= readMaybe ≡⟨ refl ⟩
    𝓰 (s $ show n) ≡⟨ DegjygirzuVeritas.pav fL∘tL n ▹ cong 𝓰 ⟩
    𝓰 (show n ∷ []) ≡⟨ refl ⟩
    𝕃.head (show n ∷ []) >>= readMaybe ≡⟨ refl ⟩
    readMaybe (show n) ≡⟨ rimco n ⟩
    just n ∎
    where
    𝓰 = readMaybe <=< 𝕃.head
    s = 𝕊.wordsBy $ T? ∘ Data.Bool.not ∘ Data.Char.isDigit
    open ≡-Reasoning

  pav : ((n : ℕ) → readMaybe (show n) ≡ just n)
      → (n : ℕ)
      → (c : Char)
      → (s : String)
      → false ≡ isDigit c
      → just n ≡ pamoinamcu (show n ++ 𝕊.fromChar c ++ s)
  pav rimco n c t j = sym $ begin
   pamoinamcu (show n ++ c' ++ t) ≡⟨ refl ⟩
   𝕃.head (d $ show n ++ c' ++ t) >>= readMaybe ≡⟨ refl ⟩
   𝓰 (d $ show n ++ c' ++ t) ≡⟨ dvr t n c j ▹ sym ▹ cong 𝓰 ⟩
   𝓰 (show n ∷ d (c' ++ t)) ≡⟨ refl ⟩
   𝕃.head (show n ∷ d (c' ++ t)) >>= readMaybe ≡⟨ refl ⟩
   readMaybe (show n) ≡⟨ rimco n ⟩
   just n ∎
   where
   dvr = DegjygirzuVeritas.rel
   c' = 𝕊.fromChar c
   𝓰 = readMaybe <=< 𝕃.head
   d = degjygirzu
   open ≡-Reasoning
\end{code}

\section{la'oi .\F{romoivimcu}.}
ni'o la .varik.\ na birti lo du'u ciksi la'oi .\F{romoivimcu}.\ fo ma kau poi ke'a zabna je cu te gerna la .lojban.

\begin{code}
romoivimcu : String → String
romoivimcu = S $ λ n → _↑ n $ 𝕃.length n ℕ.∸ 1
  where
  S = λ f → 𝕊.fromList ∘ f ∘ 𝕊.toList
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{romoivimcu}.\ mapti}

\begin{code}
module RomoivimcuVeritas where
  pav : (x : String)
      → let -1↑x = 𝕊.fromList $ (length x ℕ.∸ 1) ↓_ $ 𝕊.toList x in
        x ≡ romoivimcu x ++ -1↑x
  pav x = sym $ begin
    romoivimcu x ++ 𝕊.fromList r ≡⟨ refl ⟩
    𝕊.fromList (_↑ x' $ length x' ℕ.∸ 1) ++ 𝕊.fromList r ≡⟨ refl ⟩
    𝕊.fromList -1↓x' ++ 𝕊.fromList r ≡⟨ frokonk -1↓x' r ⟩
    𝕊.fromList (-1↓x' ++ r) ≡⟨ refl ⟩
    𝕊.fromList x'' ≡⟨ x''≡x' ▹ cong 𝕊.fromList ⟩
    𝕊.fromList x' ≡⟨ [cev∘vec]² x ▹ sym ⟩
    x ∎
    where
    x' = 𝕊.toList x
    r = _↓ x' $ length x' ℕ.∸ 1
    -1↓x' = _↑ x' $ length x' ℕ.∸ 1
    x'' = -1↓x' ++ r
    x''≡x' : x'' ≡ x'
    x''≡x' = DLP.take++drop (length x' ℕ.∸ 1) x'
    frokonk : (a b : List Char)
            → (_≡_
                (𝕊.fromList a ++ 𝕊.fromList b)
                (𝕊.fromList $ a ++ b))
    frokonk = {!!}
    [cev∘vec]² : (x : String) → x ≡ 𝕊.fromList (𝕊.toList x)
    [cev∘vec]² = {!!}
    open ≡-Reasoning
\end{code}

\section{la'oi .\F{orsygenturfa'i}.}
ni'o ro da poi ke'a ctaipe ko'a goi la'o zoi.\ \D{Fin} \B n\ .zoi.\ zo'u ro de poi ke'a ctaipe ko'a zo'u ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{orsygenturfa'i} \B s\ .zoi.\ gi ga je da dubjavme'a de gi ga je ko'a me'oi .\IC{just}.\ lo .orsi be li re bei lo .orsi be li re bei da bei de be'o bei lo ctaipe be lo su'u da dubjavme'a de gi la'oi .\B s.\ konkatena lo sinxa be da lo me'oi .comma.\ lo sinxa be de

\begin{code}
module Orsygenturfa'i where
  ps : {n : ℕ} → List Char → Maybe $ Fin n
  ps = fromℕ? <=< (readMaybe ∘ 𝕊.fromList)

  spit : String → List $ List Char
  spit = 𝕃.wordsBy (_≟ ',') ∘ 𝕊.toList

  pork : {n : ℕ}
       → List $ Maybe $ Fin n
       → Maybe $ Σ (Fin n × Fin n) $ uncurry 𝔽._≤_
  pork (just a ∷ just b ∷ []) = mapₘ (_ ,_) $ decToMaybe $ a 𝔽.≤? b
  pork _ = nothing

  orsygenturfa'i : {n : ℕ}
                 → String
                 → Maybe $ Σ (Fin n × Fin n) $ uncurry 𝔽._≤_
  orsygenturfa'i = pork ∘ 𝕃.map ps ∘ spit

open Orsygenturfa'i
  using (
    orsygenturfa'i
  )
\end{code}

\subsection{le krinu be le me'oi .\AgdaKeyword{module}.\ co'e}
ni'o pilno ko'a goi le me'oi .\AgdaKeyword{module}.\ co'e ki'u le su'u tu'a ko'a filri'a lo nu ciksi lo ctaipe be le su'u mapti  .i la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi lo steci be la'oi .\F{orgenturfa'i}.\ jenai zo'e bau la .lojban.

\subsection{le ctaipe be le su'u la'oi .\F{orsygenturfa'i}.\ mapti}

\begin{code}
module Orsygenturfa'iVeritas where
  open Orsygenturfa'i

  spit-non : (x : String) → ',' ∉ 𝕊.toList x → spit x ≡ 𝕊.toList x ∷ []
  spit-non = {!!}

  spit-du : (x z : String)
          → ',' ∉ 𝕊.toList x
          → ',' ∉ 𝕊.toList z
          → (_≡_
              (spit $ x ++ "," ++ z)
              (𝕊.toList x ∷ 𝕊.toList z ∷ []))
  spit-du x z inx inz = begin
    spit (x ++ "," ++ z) ≡⟨ refl ⟩
    w (tL $ x ++ "," ++ z) ≡⟨ tildist x ("," ++ z) ▹ cong w ⟩
    w (tL x ++ tL ("," ++ z)) ≡⟨ refl ⟩
    _ ≡⟨ tildist "," z ▹ cong (w ∘ _++_ (tL x)) ⟩
    w (tL x ++ tL "," ++ tL z) ≡⟨ refl ⟩
    w (tL x ++ ',' ∷ tL z) ≡⟨ uit _ (tL x) _ (F inx) (F inz) _ refl ⟩
    w (tL x) ++ w (tL z) ≡⟨ spit-non x inx ▹ cong (_++ _) ⟩
    (tL x ∷ []) ++ w (tL z) ≡⟨ spit-non z inz ▹ cong (_++_ _) ⟩
    (tL x ∷ []) ++ (tL z ∷ []) ≡⟨ refl ⟩
    tL x ∷ tL z ∷ [] ∎
    where
    tL = 𝕊.toList
    w = 𝕃.wordsBy $ _≟ ','
    tildist : (x z : String) → tL (x ++ z) ≡ tL x ++ tL z
    tildist = {!!}
    F : ∀ {a} → {A : Set a}
      → ⦃ _ : Truthbrary.Record.Eq.Eq A ⦄
      → {e : A}
      → {x : List A}
      → e ∉ x
      → 𝕃.All (¬_ ∘ (_≡ e)) x
    F = {!!}
    uit : ∀ {a p} → {A : Set a} → {P : Pred A p}
        → (P? : Decidable P)
        → (x z : List A)
        → 𝕃.All (¬_ ∘ P) x
        → 𝕃.All (¬_ ∘ P) z
        → (e : A)
        → P e
        → (_≡_
            (𝕃.wordsBy P? $ x ++ e ∷ z)
            (𝕃.wordsBy P? x ++ 𝕃.wordsBy P? z))
    uit = {!!}
    open ≡-Reasoning

  ps-du : ((x : ℕ) → readMaybe (show x) ≡ just x)
        → {n : ℕ}
        → (x : Fin n)
        → just x ≡ ps (𝕊.toList $ show $ 𝔽.toℕ x)
  ps-du rimco x = sym $ begin
    ps (𝕊.toList $ show x) ≡⟨ refl ⟩
    b𝔽 (rM $ id' $ show x) ≡⟨ cvd x ▹ cong (b𝔽 ∘ readMaybe) ⟩
    b𝔽 (rM $ show x) ≡⟨ rimco (𝔽.toℕ x) ▹ cong b𝔽 ⟩
    b𝔽 (just $ 𝔽.toℕ x) ≡⟨ refl ⟩
    just (𝔽.toℕ x) >>= fromℕ? ≡⟨ refl ⟩
    fromℕ? (𝔽.toℕ x) ≡⟨ refl ⟩
    mapₘ 𝔽.fromℕ< (decToMaybe $ _ ℕ.<? _) ≡⟨ refl ⟩
    _ ≡⟨ zmadekydu'i ▹ cong (mapₘ 𝔽.fromℕ<) ⟩
    mapₘ 𝔽.fromℕ< (just $ DFP.toℕ<n x) ≡⟨ refl ⟩
    just _ ≡⟨ DFP.fromℕ<-toℕ _ _ ▹ cong just ⟩
    just x ∎
    where
    rM = readMaybe
    b𝔽 = _>>= fromℕ?
    id' = 𝕊.fromList ∘ 𝕊.toList
    open ≡-Reasoning
    cvd : {n : ℕ} → (x : Fin n) → id' (show x) ≡ show x
    cvd x = istu $ show x
      where
      istu : (x : String) → id' x ≡ x
      istu = {!!}

  ps-nada : (j : String)
          → ¬_ $ Σ (∃ Fin) $ _≡_ j ∘ show ∘ proj₂
          → {n : ℕ}
          → nothing ≡ ps {n = n} (𝕊.toList j)
  ps-nada = {!!}

  pork-du : {n : ℕ}
          → {x z : Fin n}
          → (djb : x 𝔽.≤ z)
          → (_≡_
              (pork $ just x ∷ just z ∷ [])
              (just $ (x , z) , djb))
  pork-du {n} {x} {z} djb = begin
    pork (just x ∷ just z ∷ []) ≡⟨ refl ⟩
    mapₘ (_ ,_) (decToMaybe $ x 𝔽.≤? z) ≡⟨ refl ⟩
    _ ≡⟨ zmadekydu'i {m = djb} ▹ cong (mapₘ (_ ,_)) ⟩
    mapₘ (_ ,_) (just djb) ≡⟨ refl ⟩
    just ((x , z) , djb) ∎
    where
    open ≡-Reasoning

  pork-nada : {n : ℕ}
            → {x z : Fin n}
            → ¬_ $ x 𝔽.≤ z
            → pork (just x ∷ just z ∷ []) ≡ nothing
  pork-nada {_} {x} {z} j = begin
    pork (just x ∷ just z ∷ []) ≡⟨ refl ⟩
    mapₘ (_ ,_) (decToMaybe $ x 𝔽.≤? z) ≡⟨ refl ⟩
    _ ≡⟨ DN ▹ proj₂ ▹ cong (mapₘ (_ ,_) ∘ decToMaybe) ⟩
    mapₘ (_ ,_) (decToMaybe $ no $ proj₁ DN) ≡⟨ refl ⟩
    nothing ∎
    where
    DN = Relation.Nullary.Decidable.dec-no (x 𝔽.≤? z) j
    open ≡-Reasoning

  pav : ((x : ℕ) → readMaybe (show x) ≡ just x)
      → {n : ℕ}
      → (a b : Fin n)
      → (djb : a 𝔽.≤ b)
      → (_≡_
          (orsygenturfa'i $ show a ++ "," ++ show b)
          (just $ (a , b) , djb))
  pav rimco a b djb = begin
    orsygenturfa'i (show a ++ "," ++ show b) ≡⟨ refl ⟩
    pork (𝕃.map ps $ spit a,b) ≡⟨ cong pork mapyjus ⟩
    pork (just a ∷ just b ∷ []) ≡⟨ pork-du djb ⟩
    just ((a , b) , djb) ∎
    where
    a,b = show a ++ "," ++ show b

    open ≡-Reasoning
    mapyjus = begin
      𝕃.map ps (spit a,b) ≡⟨ spidus a b ▹ cong (𝕃.map ps) ⟩
      𝕃.map ps (showF' a ∷ showF' b ∷ []) ≡⟨ refl ⟩
      𝕃.map justF' (a ∷ b ∷ []) ≡⟨ justymapdu $ a ∷ b ∷ [] ⟩
      𝕃.map just (a ∷ b ∷ []) ≡⟨ refl ⟩
      just a ∷  just b ∷ [] ∎
      where
      showF' : {n : ℕ} → Fin n → List Char
      showF' = 𝕊.toList ∘ show
      justF' : {n : ℕ} → Fin n → Maybe $ Fin n
      justF' = ps ∘ showF'
      justF'≡just : {n : ℕ} → (x : Fin n) → justF' x ≡ just x
      justF'≡just x = sym $ ps-du rimco x
      justymapdu : {n : ℕ}
                 → (L : List $ Fin n)
                 → 𝕃.map justF' L ≡ 𝕃.map just L
      justymapdu = DLP.map-cong justF'≡just
      spidus : {n : ℕ}
             → (a b : Fin n)
             → (_≡_
                 (spit $ show a ++ "," ++ show b)
                 (showF' a ∷ showF' b ∷ []))
      spidus a b = spit-du (show a) (show b) (nokom a) (nokom b)
        where
        nokom : {n : ℕ} → (x : Fin n) → ',' ∉ 𝕊.toList (show x)
        nokom = {!!}
\end{code}

\section{la'oi .\F{orsygenturfa'i₃}.}
ni'o ro da xi pa poi ke'a ctaipe ko'a goi la'o zoi.\ \D{Fin} \B n\ .zoi.\ zo'u ro da xi re poi ke'a ctaipe ko'a zo'u do da xi ci poi ke'a ctaipe ko'a zo'u ro de poi ctaipe lo su'u ke'a cmima lo'i ro lerfu po le glibau ge'u poi ke'a me'oi .minuscule.\ zo'u ga jonai ko'e goi la'o zoi.\ \F{orsygenturfa'i₃} \B x\ .zoi.\ du la'oi .\IC{nothing}.\ gi ga je la'oi .\B x.\ konkatena lo sinxa be da xi pa lo me'oi .comma.\ lo sinxa be da xi re de lo sinxa be da xi ci gi ko'e me'oi .\IC{just}.\ lo .orsi be li re bei lo .orsi be li re bei lo .orsi be li re bei da xi pa bei da xi re be'o bei zo'e be'o bei da xi ci

\begin{code}
module Orsygenturfa'i₃ where
  lispork : List $ List String → Maybe $ (String × String) × String
  lispork ((a ∷ []) ∷ (b ∷ c ∷ []) ∷ []) = just $ (a , b) , c
  lispork _ = nothing

  orsispita : String → Maybe $ (String × String) × String
  orsispita = lispork ∘ 𝕃.map (w aintDigit?) ∘ w (_≟ ',')
    where
    w = 𝕊.wordsBy
    aintDigit? = T? ∘ Data.Bool.not ∘ isDigit

  pork : {n : ℕ}
       → (String × String) × String
       → Maybe $ Σ (Fin n × Fin n) (uncurry 𝔽._≤_) × Fin n
  pork ((a , b) , c)= ax ,ₘ readMaybe c
    where
    ax = R >>= λ (a' , b') → mapₘ (f a' b') $ decToMaybe $ a' 𝔽.≤? b'
      where
      f = _,_ ∘₂ _,_
      R = readMaybe a ,ₘ readMaybe b

  orsygenturfa'i₃ : {n : ℕ}
                  → String
                  → (Maybe $ _×_
                      (Σ (Fin n × Fin n) (uncurry 𝔽._≤_))
                      (Fin n))
  orsygenturfa'i₃ = pork <=< orsispita

open Orsygenturfa'i₃
  using (
    orsygenturfa'i₃
  )
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{orsygenturfa'i₃}.\ mapti}

\begin{code}
module Orsygenturfa'i₃Veritas where
  open Orsygenturfa'i₃

  lisporv : (a b c : String)
          → (_≡_
              (lispork $ (a ∷ []) ∷ (b ∷ c ∷ []) ∷ [])
              (just $ (a , b) , c))
  lisporv _ _ _ = refl

  lisporn : (x : List $ List String)
          → (¬_
              (Σ (String × String × String)
              (λ (a , b , c) →
                (x ≡ (a ∷ []) ∷ (b ∷ c ∷ []) ∷ []))))
          → lispork x ≡ nothing
  lisporn = {!!}

  orspiv : (a b c : ℕ)
         → (x : Char)
         → false ≡ isDigit x
         → let x' = 𝕊.fromChar x in
           (_≡_
             (just $ (show a , show b) , show c)
             (orsispita
               (show a ++ "," ++ show b ++ x' ++ show c)))
  orspiv a b c x j = sym $ begin
    orsispita K ≡⟨ refl ⟩
    L (𝕃.map (w aD?) $ w (_≟ ',') $ K) ≡⟨ {!!} ⟩
    L' (𝕃.map (w' aD?) $ w' (_≟ ',') $ K') ≡⟨ {!!} ⟩
    L' (𝕃.map (w' aD?) $ s' a ∷ [ s'bxs'c ]) ≡⟨ refl ⟩
    L' (w' aD? (s' a) ∷ 𝕃.map (w' aD?) [ s'bxs'c ]) ≡⟨ refl ⟩
    _ ≡⟨ uadysas a ▹ cong (L' ∘ (_∷ 𝕃.map (w' aD?) [ s'bxs'c ])) ⟩
    L' ([ s' a ] ∷ 𝕃.map (w' aD?) [ s'bxs'c ]) ≡⟨ refl ⟩
    L' ([ s' a ] ∷ [ w' aD? s'bxs'c ])  ≡⟨ refl ⟩
    _ ≡⟨ sabus ▹ cong (L' ∘ _∷_ ([ s' a ]) ∘ [_]) ⟩
    L' ([ s' a ] ∷ [ s' b ∷ [ s' c ] ]) ≡⟨ refl ⟩
    L' (map₂ s' abj) ≡⟨ refl ⟩
    L (map₂ (𝕊.fromList ∘ s') abj) ≡⟨ map₂-cong fL∘tL _ ▹ cong L ⟩
    L (map₂ s abj) ≡⟨ refl ⟩
    just ((show a , show b) , show c) ∎
    where
    L = lispork
    [_] = 𝕃.[_]
    w = 𝕊.wordsBy
    w' = 𝕃.wordsBy
    aD? = T? ∘ Data.Bool.not ∘ isDigit
    K = show a ++ "," ++ show b ++ 𝕊.fromChar x ++ show c
    s = show
    s' = 𝕊.toList ∘ show
    s'bxs'c = s' b ++ x ∷ s' c
    fL∘tL : (x : String) → 𝕊.fromList (𝕊.toList x) ≡ x
    fL∘tL = {!!}
    K' = s' a ++ ',' ∷ s' b ++ x ∷ s' c
    abj = [ a ] ∷ [ b ∷ [ c ] ]
    sabus : w' aD? s'bxs'c ≡ s' b ∷ [ s' c ]
    sabus = {!!}
    uadysas : (a : ℕ) → w' aD? (s' a) ≡ [ s' a ]
    uadysas = {!!}
    map₂ : ∀ {a b} → {A : Set a} → {B : Set b}
         → (A → B) → List $ List A → List $ List B
    map₂ = 𝕃.map ∘ 𝕃.map
    L' : List $ List $ List $ Char
       → Maybe $ (String × String) × String
    L' = L ∘ 𝕃.map (𝕃.map 𝕊.fromList)
    open ≡-Reasoning
    map₂-cong = DLP.map-cong ∘ DLP.map-cong

  porkcos : {n : ℕ}
          → (a b : Fin n)
          → (d : a 𝔽.≤ b)
          → (c : Fin n)
          → (_≡_
              (pork $ (show a , show b) , show c)
              (just $ ((a , b) , d) , c))
  porkcos a b d c = begin
    pork ((show a , show b) , show c) ≡⟨ refl ⟩
    _,ₘ_ ax (readMaybe $ show c) ≡⟨ rimcos c ▹ cong (_,ₘ_ ax) ⟩
    _,ₘ_ ax (just c) ≡⟨ ax≡justabd ▹ cong (flip _,ₘ_ $ just c) ⟩
    _,ₘ_ (just $ (a , b) , d) (just c) ≡⟨ refl ⟩
    just (((a , b) , d) , c) ∎
    where
    ax : Maybe $ Σ (Fin _ × Fin _) $ uncurry 𝔽._≤_
    ax = R >>= λ (a' , b') → mapₘ (f a' b') $ decToMaybe $ a' 𝔽.≤? b'
      where
      f = λ a b x → (a , b) , x
      R = readMaybe (show a) ,ₘ readMaybe (show b)
    rimcos : {n : ℕ} → (x : Fin n) → readMaybe (show x) ≡ just x
    rimcos = {!!}
    open ≡-Reasoning
    ax≡justabd : ax ≡ just ((a , b) , d)
    ax≡justabd = {!!}

  pav : {n : ℕ}
      → (v x z : Fin n)
      → (d : v 𝔽.≤ x)
      → (c : Char)
      → false ≡ isDigit c
      → (_≡_
          (just $ ((v , x) , d) , z)
          (orsygenturfa'i₃
            (let c' = 𝕊.fromChar c in
             show v ++ "," ++ show x ++ c' ++ show z)))
  pav v x z d c j = sym $ begin
    orsygenturfa'i₃ (k₃ v x c z) ≡⟨ refl ⟩
    orsispita (k₃ v x c z) >>= pork ≡⟨ refl ⟩
    orsispita (k₃ (t v) (t x) c $ t z) >>= pork ≡⟨ refl ⟩
    _ ≡⟨ orspiv (t v) (t x) (t z) c j ▹ sym ▹ cong (_>>= pork) ⟩
    just ((show (t v) , show (t x)) , show (t z)) >>= pork ≡⟨ refl ⟩
    pork ((show (t v) , show (t x)) , show (t z)) ≡⟨ refl ⟩
    pork ((show v , show x) , show z) ≡⟨ porkcos v x d z ⟩
    just (((v , x) , d) , z) ∎
    where
    t = 𝔽.toℕ
    k₃ : ∀ {a b c} → {A : Set a} → {B : Set b} → {C : Set c}
       → ⦃ Show A ⦄ → ⦃ Show B ⦄ → ⦃ Show C ⦄
       → A → B → Char → C → String
    k₃ v x c z = show v ++ "," ++ show x ++ c' ++ show z
      where
      c' = 𝕊.fromChar c
    open ≡-Reasoning
\end{code}

\section{la'oi .\F{reed}.}
ni'o ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{reed} \B x \B s\ .zoi.\ gi ga je la'oi .\B s.\ midnoi fo la'o zoi.\ \Xr{ed}{1} .zoi.\ je cu mapti la'o zoi.\ \D{Cmd} \B x\ .zoi.\ gi ko'a me'oi .\IC{just}.\ lo mapti be la'oi .\B s.

\begin{code}
module Reed where
  module No where
    g : {x : Buffer} → Char → Maybe $ Cmd x
    g {x} 'w' = mapₘ Rejgau $ Buffer.datnyveicme x
    g 'u' = mapₘ Xruti $ 𝕃.head $ 𝕃.allFin _
    g 'q' = just Sisti
    g 'Q' = just Sisti!
    g _ = nothing

    k : {x : Buffer} → List String → Maybe $ Cmd x
    k ("w" ∷ xs@(_ ∷ _)) = just $ Rejgau $ 𝕊.unwords xs
    k _ = nothing

    t : {x : Buffer} → String → Maybe $ Cmd x
    t = g <=< (𝕃.head ∘ 𝕊.toList)

  module Pa where
    g : {x : Buffer} → Buffer.F x → Char → Maybe $ Cmd x
    g n 'a' = just $ Jmina n
    g n 'i' = just $ Jmini n
    g _ _ = nothing

    t : {x : Buffer} → String → Maybe $ Cmd x
    t {x} s = uncurry g =<<_ $ _,ₘ_ n $ 𝕃.last $ 𝕊.toList s
      where
      n = pamoinamcu s >>= fromℕ?

  module Re where
    g : (x : Buffer)
      → (a b : Buffer.F x)
      → (a 𝔽.≤ b)
      → Char
      → Maybe $ Cmd x
    g x a b z j with j
    ... | 'c' = just $ Basti a b z
    ... | 'd' = just $ Vimcu a b z
    ... | 'n' = just $ Namcusku a b z
    ... | 'p' = just $ Cusku a b z
    ... | _ = nothing

    t : (x : Buffer) → String → Maybe $ Cmd x
    t x s = _>>= g' $ (Data.Maybe.ap ∘₂ mapₘ) _,_ (romoi s) og
      where
      og = orsygenturfa'i $ romoivimcu s
      romoi = 𝕃.last ∘ 𝕊.toList
      g' = λ (r' , _ , z) → g x _ _ z r'

  module Ci where
    g : {x : Buffer}
      → (a b c : Buffer.F x)
      → (a 𝔽.≤ b)
      → Char
      → Maybe $ Cmd x
    g a b c d x with x
    ... | 'm' = just $ Muvgau a b c d
    ... | _ = nothing

    t : {x : Buffer} → String → Maybe $ Cmd x
    t {x} s = g' =<<_ $ c ,ₘ orsygenturfa'i₃ s
      where
      g' = λ (z , (_ , d) , c) → g _ _ c d z
      c = f $ 𝕃.filter aintDigit? $ 𝕊.toList s
        where
        aintDigit? = T? ∘ Data.Bool.not ∘ isDigit
        f : _ → _
        f (x ∷ []) = just x
        f _ = nothing

  reed : (x : Buffer) → String → Maybe $ Cmd x
  reed x s = 𝕃.head $ 𝕃.mapMaybe id terp
    where
    terp : List $ Maybe $ Cmd x
    terp = No.t s ∷ Pa.t s ∷ Re.t x s ∷ No.k s' ∷ []
      where
      s' = 𝕊.wordsBy (_≟ ' ') s

open Reed
  using (
    reed
  )
\end{code}

\subsection{le krinu be le me'oi .\AgdaKeyword{module}.\ co'e}
ni'o pilno ko'a goi le me'oi .\AgdaKeyword{module}.\ co'e ki'u le su'u tu'a ko'a filri'a lo nu ciksi lo ctaipe be le su'u mapti  .i la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi lo steci be la'oi .\F{reed}.\ jenai zo'e bau la .lojban.

\subsection{le cmene be le me'oi .\AgdaKeyword{module}.\ fancu}
ni'o zo .k.\ cmavlaka'i zo konkatena

.i zo .t.\ cmavlaka'i zo tolsti

.i cumki fa lo nu su'o da zo'u zo .g.\ cmavlaka'i da

\subsection{le ctaipe be le su'u la'oi .\F{reed}.\ mapti}

\begin{code}
module ReedVeritas where
  private
    k₁ : (x : Buffer)
       → (a : Buffer.F x)
       → Char
       → String
    k₁ _ a x = show (𝔽.toℕ a) ++ 𝕊.fromChar x

    k₂ : (x : Buffer)
       → (a b : Buffer.F x)
       → Char
       → String
    k₂ _ a b x = f a ++ "," ++ f b ++ 𝕊.fromChar x
      where
      f = show ∘ 𝔽.toℕ

    k₃ : (x : Buffer)
       → (a b c : Buffer.F x)
       → Char
       → String
    k₃ x a b c s = k₂ x a b s ++ show (𝔽.toℕ c)

  uin : (x : Buffer)
      → reed x "w" ≡ mapₘ Rejgau (Buffer.datnyveicme x)
  uin x = begin
    reed x "w" ≡⟨ refl ⟩
    𝕃.head (𝕃.mapMaybe id L) ≡⟨ duridos ⟩
    𝕃.head (𝕊.toList "w") >>= Reed.No.g ≡⟨ refl ⟩
    mapₘ Rejgau (Buffer.datnyveicme x) ∎
    where
    open Reed
    ridos = 𝕃.head (𝕊.toList "w") >>= Reed.No.g
    L = ridos ∷ _
    duridos : 𝕃.head (𝕃.mapMaybe id L) ≡ ridos
    duridos with ridos
    ... | just _ = refl
    ... | nothing = refl
    open ≡-Reasoning

  -- ni'o la .varik. cu stidi lo nu tcidu le velcki be
  -- la .uin. fa lo na jimpe be fi la .kybin. je la'oi
  -- .kybin'.

  kybin : (x : Buffer)
        → reed x "q" ≡ just Sisti
  kybin _ with 𝕃.head (𝕊.toList "q") >>= Reed.No.g
  ... | just _ = refl
  ... | nothing = refl

  kybin' : (x : Buffer)
         → reed x "Q" ≡ just Sisti!
  kybin' _ with 𝕃.head (𝕊.toList "Q") >>= Reed.No.g
  ... | just _ = refl
  ... | nothing = refl

  xon : (x : Buffer)
      → (z : ∃ λ n → ℕ.suc n ≡ length (Buffer.citri x))
      → reed x "u" ≡ just (Xruti $ mink 𝔽.zero $ proj₂ z)
  xon x z = begin
    reed x "u" ≡⟨ refl ⟩
    𝕃.head (𝕃.mapMaybe id terp') ≡⟨ xedrenod 3 $ Reed.No.t "u" ⟩
    𝕃.head (𝕃.mapMaybe id $ Reed.No.t "u" ∷ []) ≡⟨ noxed _ ▹ sym ⟩
    Reed.No.t "u" ≡⟨ refl ⟩
    mapₘ X (𝕃.head $ 𝕃.allFin _) ≡⟨ dzeroxe z ▹ cong (mapₘ X) ⟩
    just (X $ mink 𝔽.zero $ proj₂ z) ∎
    where
    X = Xruti
    terp' = Reed.No.t "u" ∷ 𝕃.replicate 3 nothing
    dzeroxe : {n : ℕ}
            → (z : ∃ $ (_≡ n) ∘ ℕ.suc)
            → 𝕃.head (𝕃.allFin n) ≡ just (mink 𝔽.zero $ proj₂ z)
    dzeroxe (_ , refl) = refl
    noxed : ∀ {a} → {A : Set a}
          → (x : Maybe A)
          → x ≡ 𝕃.head (𝕃.mapMaybe id $ x ∷ [])
    noxed nothing = refl
    noxed (just _) = refl
    xedrenod : ∀ {a} → {A : Set a}
             → (n : ℕ)
             → (x : Maybe A)
             → ((_≡_ on_ $ 𝕃.head ∘ 𝕃.mapMaybe id ∘ _∷_ x)
                 (𝕃.replicate n nothing)
                 [])
    xedrenod _ (just _) = refl
    xedrenod 0 nothing = refl
    xedrenod (ℕ.suc n) nothing = xedrenod n nothing
    open ≡-Reasoning

  ac : (x : Buffer)
     → (a : Buffer.F x)
     → just (Jmina a) ≡ reed x (k₁ x a 'a')
  ac x a = sym $ begin
    reed x (k₁ x a 'a') ≡⟨ refl ⟩
    reed x K ≡⟨ {!!} ⟩
    Reed.Pa.t K ≡⟨ {!!} ⟩
    _,ₘ_ (pamoinamcu K >>= fromℕ?) (sl "a") >>= g' ≡⟨ {!!} ⟩
    _,ₘ_ (rms a) (sl "a") >>= g' ≡⟨ refl ⟩
    _,ₘ_ (rms a) (just 'a') >>= g' ≡⟨ refl ⟩
    _ ≡⟨ rimco a ▹ cong (λ x → _,ₘ_ x _ >>= g') ⟩
    _,ₘ_ (just a) (just 'a') >>= g' ≡⟨ refl ⟩
    just (a , 'a') >>= g' ≡⟨ refl ⟩
    Reed.Pa.g a 'a' ≡⟨ refl ⟩
    just (Jmina a) ∎
    where
    g' = uncurry Reed.Pa.g
    K = k₁ x a 'a'
    rms : {n : ℕ} → Fin n → Maybe $ Fin n
    rms = readMaybe ∘ show
    sl = 𝕃.last ∘ 𝕊.toList
    rimco : {n : ℕ} → (x : Fin n) → rms x ≡ just x
    rimco = {!!}
    open ≡-Reasoning

  ic : (x : Buffer)
     → (a : Buffer.F x)
     → just (Jmini a) ≡ reed x (k₁ x a 'i')
  ic = {!!}

  mixer : (x : Buffer)
        → (a b c : Buffer.F x)
        → (d : a 𝔽.≤ b)
        → just (Muvgau a b c d) ≡ reed x (k₂ x a b 'm')
  mixer x a b c d = {!!}

  vim : (x : Buffer)
      → (a b : Buffer.F x)
      → (d : a 𝔽.≤ b)
      → just (Vimcu a b d) ≡ reed x (k₂ x a b 'd')
  vim x a b d = sym $ begin
    reed x (k₂ x a b 'd') ≡⟨ {!!} ⟩
    Reed.Re.t x (k₂ x a b 'd') ≡⟨ {!!} ⟩
    Reed.Re.g x a b d 'd' ≡⟨ refl ⟩
    just (Vimcu a b d) ∎
    where
    open ≡-Reasoning

  uip : ((s : String) → s ≡_ $ 𝕊.unwords $ 𝕊.wordsBy (_≟ ' ') s)
      → (x : Buffer)
      → (s : String)
      → (c : Char)
      → ¬ (c ≡ ' ')
      → let c∷s = 𝕊.fromChar c ++ s in
        Data.Maybe.Is-just $ 𝕃.uncons $ 𝕊.wordsBy (_≟ ' ') c∷s
      → just (Rejgau c∷s) ≡ reed x ("w " ++ c∷s)
  uip unwords∘f x s c n uj = sym $ begin
    reed x ("w " ++ c∷s) ≡⟨ w++s≡w++fs ▹ cong (reed x) ⟩
    reed x (unwords $ "w" ∷ f c∷s) ≡⟨ {!!} ⟩
    k (f $ unwords $ "w" ∷ f c∷s) ≡⟨ f∘unwords _ ▹ cong k ⟩
    k ("w" ∷ f c∷s) ≡⟨ f[c∷s]≡v₁∷v₂ ▹ cong (k ∘ _∷_ "w") ⟩
    k ("w" ∷ v₁ ∷ v₂) ≡⟨ refl ⟩
    j∘R (unwords $ v₁ ∷ v₂) ≡⟨ refl ⟩
    j∘R _ ≡⟨ f[c∷s]≡v₁∷v₂ ▹ sym ▹ cong (j∘R ∘ unwords) ⟩
    j∘R (unwords $ f c∷s) ≡⟨ unwords∘f c∷s ▹ sym ▹ cong j∘R ⟩
    j∘R c∷s ∎
    where
    open Reed.No using (k)
    c∷s = 𝕊.fromChar c ++ s
    f = 𝕊.wordsBy $ _≟ ' '
    v = Data.Maybe.to-witness uj
    v₁ = proj₁ v
    v₂ = proj₂ v
    j∘R = just ∘ Rejgau
    f[c∷s]≡v₁∷v₂ : f c∷s ≡ v₁ ∷ v₂
    f[c∷s]≡v₁∷v₂ = consunwords uj
      where
      consunwords : ∀ {a} → {A : Set a}
                  → {xs : List A}
                  → (j : Data.Maybe.Is-just $ 𝕃.uncons xs)
                  → let j' = Data.Maybe.to-witness j in
                    xs ≡ proj₁ j' ∷ proj₂ j'
      consunwords {xs = X@(x ∷ xs)} j = sym $ begin
        proj₁ j' ∷ proj₂ j' ≡⟨ {!!} ⟩
        x ∷ xs ≡⟨ refl ⟩
        X ∎
        where
        j' = Data.Maybe.to-witness j
        open ≡-Reasoning
    unwords = 𝕊.unwords
    open Reed
    open ≡-Reasoning
    f∘unwords : (x : List String) → f (unwords x) ≡ x
    f∘unwords = {!!}
    w++s≡w++fs : "w " ++ c∷s ≡ unwords ("w" ∷ f c∷s)
    w++s≡w++fs = {!!}
\end{code}

\section{la \F{kanji}}
ni'o la'o zoi.\ \F{kanji} \Sym\{\B x\Sym\} \B s\ .zoi.\ .orsi li re lo jalge be lo nu co'e la'oi .\B s.\ la'oi .\B x.\ kei zo'e poi ga jonai ke'a du la'oi .\IC{nothing}.\ gi ga jonai cadga fa lo nu cusku ke'a fo lo co'e co mu'oi glibau.\ standard output .glibau.\ gi\ldots ga je co'e gi la .varik.\ na birti lo du'u zabna ciksi fo ma kau bau la .lojban.  .i ku'i gu zabna ciksi bau la .lojban.\ gi ciksi le ctaipe be le su'u mapti

\begin{code}
kanji : {x : Buffer}
      → Cmd x
      → Σ Buffer $ Maybe ∘ _⊎_ String ∘ Cmdᵢₒ
kanji {x} Sisti = x ,_ $ just $ inj₂ Sistiᵢₒ
kanji {x} Sisti! = x ,_ $ just $ inj₂ Sisti!ᵢₒ
kanji {x} (Jmina a) = x ,_ $ just $ inj₂ $ Tciduᵢₒ "/dev/stdin" a
kanji {x} (Cusku a b _) = x ,_ $ just $ inj₁ $ unlines $ i BL
  where
  BL = Buffer.lerpinste x
  i = (𝔽.toℕ a) ↓_ ∘ (𝔽.toℕ b ℕ.+ 1) ↑_
kanji {x} (Namcusku a b m) = x ,_ $ just $ inj₁ $ viiet kot
  where
  kot = from-inj₁ $ from-just $ proj₂ $ kanji {x} $ Cusku a b m
  viiet = unlines ∘ 𝕃.map stringCat' ∘ uin ∘ lines
    where
    stringCat' = λ (x , z) → show x ++ "\t" ++ z
    uin : List String → List $ ℕ × String
    uin = 𝕃.zip $ 𝔽.toℕ a ↓_ $ 𝕃.upTo $ 𝔽.toℕ b ℕ.+ 1
kanji {x} (Muvgau a b c _) = x' , nothing
  where
  x' = record x {
    citri = Buffer.cninycitri x;
    cablerpinsle = mink (Buffer.cablerpinsle x) {!!};
    lerpinste = 𝔽.toℕ a ↑ BL ++ {!!} ++ {!!}
    }
    where
    BL = Buffer.lerpinste x
kanji {x} (Vimcu a b _) = x' , nothing
  where
  x' = record x {
    citri = Buffer.cninycitri x;
    cablerpinsle = {!!};
    lerpinste = 𝔽.toℕ a ↑ Lz ++ ℕ.suc (𝔽.toℕ b) ↓ Lz}
    where
    Lz = Buffer.lerpinste x
kanji {x} (Jmini a) = {!!}
kanji {x} (Rejgau d) = x ,_ $ just $ inj₂ $ Rejgauᵢₒ xl d
  where
  xl = unlines $ Buffer.lerpinste x
kanji {x} (Basti a b d) = kanji {x'} $ Jmina a∸1'
  where
  a∸1' = {!!}
  x' = proj₁ $ kanji {x} $ Vimcu a b d
  a∸1'≡z : 𝔽.toℕ a∸1' ≡ 𝔽.toℕ a ℕ.∸ 1
  a∸1'≡z = {!!}
kanji {x} (Xruti n) = {!!}
\end{code}

\subsection{le ctaipe be le su'u la \F{kanji}\ cu mapti}

\begin{code}
module KanjyVeritas where
  sistid : (x : Buffer)
         → kanji {x} Sisti ≡_ $ x , just (inj₂ Sistiᵢₒ)
  sistid x = refl

  sistik : (x : Buffer)
         → kanji {x} Sisti! ≡_ $ x , just (inj₂ Sisti!ᵢₒ)
  sistik x = refl

  dub₂ : (x : Buffer)
       → (a b : Buffer.F x)
       → (d : a 𝔽.≤ b)
       → let K = λ f → kanji $ f a b d in
         let i = _≡_ x ∘ proj₁ ∘ K in
         i Cusku × i Namcusku
  dub₂ _ _ _ _ = refl , refl

  jminac : (x : Buffer)
         → (a : Buffer.F x)
         → (_≡_
             (kanji {x} $ Jmina a)
             (x ,_ $ just $ inj₂ $ Tciduᵢₒ "/dev/stdin" a))
  jminac _ _ = refl

  nilzilcmiv : (x : Buffer)
             → (a b : Buffer.F x)
             → (d : a 𝔽.≤ b)
             → let BLT = length ∘ Buffer.lerpinste in
               (_≡_
                 (BLT $ proj₁ $ kanji {x} $ Vimcu a b d)
                 (BLT x ℕ.∸_ $ ℕ.suc $ 𝔽.toℕ b ℕ.∸ 𝔽.toℕ a))
  nilzilcmiv x a b d = begin
    lb x₂ ≡⟨ refl ⟩
    length (𝔽.toℕ a ↑ Lz ++ ℕ.suc (𝔽.toℕ b) ↓ Lz) ≡⟨ refl ⟩
    length (a' ↑ Lz ++ b'+1 ↓ Lz) ≡⟨ DLP.length-++ $ a' ↑ Lz ⟩
    length (a' ↑ Lz) ℕ.+ length (b'+1 ↓ Lz) ≡⟨ refl ⟩
    _ ≡⟨ DLP.length-drop b'+1 Lz ▹ cong (ℕ._+_ _) ⟩
    length (a' ↑ Lz) ℕ.+ (length Lz ℕ.∸ b'+1) ≡⟨ refl ⟩
    length (a' ↑ Lz) ℕ.+ (lb x ℕ.∸ b'+1) ≡⟨ {!!} ⟩
    a' ℕ.+ (lb x ℕ.∸ b'+1) ≡⟨ DNP.+-comm a' _ ⟩
    lb x ℕ.∸ b'+1 ℕ.+ a' ≡⟨ v∸x+z≡v∸[x∸z] $ flex d ⟩
    lb x ℕ.∸ (b'+1 ℕ.∸ a') ≡⟨ refl ⟩
    lb x ℕ.∸ (ℕ.suc b' ℕ.∸ a') ≡⟨ {!!} ⟩
    lb x ℕ.∸ ℕ.suc (b' ℕ.∸ a') ≡⟨ refl ⟩
    lb x ℕ.∸ ℕ.suc (𝔽.toℕ b ℕ.∸ 𝔽.toℕ a) ∎
    where
    b' = 𝔽.toℕ b
    b'+1 = ℕ.suc b'
    a' = 𝔽.toℕ a
    Lz = Buffer.lerpinste x
    x₂ = proj₁ $ kanji {x} $ Vimcu a b d
    lb = length ∘ Buffer.lerpinste
    flex : {a : ℕ}
         → {m n : Fin a}
         → n 𝔽.≤ m
         → 𝔽.toℕ n ℕ.≤ ℕ.suc (𝔽.toℕ m)
    flex = {!!}
    open ≡-Reasoning
    v∸x+z≡v∸[x∸z] : {v x z : ℕ}
                 → z ℕ.≤ x
                 → v ℕ.∸ x ℕ.+ z ≡ v ℕ.∸ (x ℕ.∸ z)
    v∸x+z≡v∸[x∸z] {z = 0} ℕ.z≤n = n+0≡n _
      where
      n+0≡n : (n : ℕ) → n ℕ.+ 0 ≡ n
      n+0≡n 0 = refl
      n+0≡n (ℕ.suc n) = n+0≡n n ▹ cong ℕ.suc
    v∸x+z≡v∸[x∸z] {v} {x} {z = ℕ.suc z} (ℕ.s≤s s) = begin
      v ℕ.∸ x ℕ.+ ℕ.suc z ≡⟨ {!!} ⟩
      v ℕ.∸ ℕ.suc (x ℕ.+ z) ≡⟨ {!!} ⟩
      v ℕ.∸ (x ℕ.∸ ℕ.suc z) ∎

  takeduv : (x : Buffer)
          → (a b : Buffer.F x)
          → (d : a 𝔽.≤ b)
          → let x₂ = proj₁ $ kanji {x} $ Vimcu a b d in
            (_≡_ on ((𝔽.toℕ a) ↑_ ∘ Buffer.lerpinste)) x x₂
  takeduv x a b d = sym $ begin
    BLT (proj₁ $ kanji {x} $ Vimcu a b d) ≡⟨ refl ⟩
    𝔽.toℕ a ↑ (BLT x ++ BLD x) ≡⟨ refl ⟩
    𝔽.toℕ a ↑ ((𝔽.toℕ a ↑ BL x) ++ BLD x) ≡⟨ teikteik _ _ ⟩
    BLT x ∎
    where
    BL = Buffer.lerpinste
    BLT = (𝔽.toℕ a) ↑_ ∘ BL
    BLD = ℕ.suc (𝔽.toℕ b) ↓_ ∘ BL
    open ≡-Reasoning
    teikteik : ∀ {a} → {A : Set a}
             → (x : List A)
             → {z : List A}
             → (n : Fin $ length x)
             → let n' = 𝔽.toℕ n in
               n' ↑ (n' ↑ x ++ z) ≡ n' ↑ x
    teikteik (_ ∷ _) 𝔽.zero = refl
    teikteik (_ ∷ _) (𝔽.suc _) = teikteik _ _ ▹ cong (_ ∷_)

  dropyduv : (x : Buffer)
           → (a b : Buffer.F x)
           → (d : a 𝔽.≤ b)
           → let x₂ = proj₁ $ kanji {x} $ Vimcu a b d in
             (_≡_
               (ℕ.suc (𝔽.toℕ b) ↓ Buffer.lerpinste x)
               (𝔽.toℕ a ↓ Buffer.lerpinste x₂))
  dropyduv x a b d = sym $ begin
    𝔽.toℕ a ↓ BL x₂ ≡⟨ refl ⟩
    a' ↓ (a' ↑ BL x ++ b'++ ↓ BL x) ≡⟨ teikteikdrop (BL x) _ a ⟩
    b'++ ↓ BL x ∎
    where
    a' = 𝔽.toℕ a
    b'++ = ℕ.suc $ 𝔽.toℕ b
    BL = Buffer.lerpinste
    x₂ = proj₁ $ kanji {x} $ Vimcu a b d
    teikteikdrop : ∀ {a} → {A : Set a}
                 → (x z : List A)
                 → (n : Fin $ length x)
                 → 𝔽.toℕ n ↓ (𝔽.toℕ n ↑ x ++ z) ≡ z
    teikteikdrop (_ ∷ _) _ 𝔽.zero = refl
    teikteikdrop (_ ∷ xs) z (𝔽.suc n) = teikteikdrop xs z n
    open ≡-Reasoning

  pindices : (x : Buffer)
           → (a b : Buffer.F x)
           → (d : a 𝔽.≤ b)
           → let K = proj₂ $ kanji {x} $ Cusku a b d in
             let L = lines $ from-inj₁ $ from-just K in
             let Lx = Buffer.lerpinste x in
             (n : Fin $ length L)
           → (Σ
               (𝔽.toℕ n ℕ.+ 𝔽.toℕ a ℕ.< length Lx)
               (λ ℓ → L ! n ≡ Lx ! 𝔽.fromℕ< ℓ))
  pindices x a b d n = {!!} , {!!}

  muvduzilcmi : (x : Buffer)
              → (a b c : Buffer.F x)
              → (d : a 𝔽.≤ b)
              → ((_≡_ on (length ∘ Buffer.lerpinste))
                  x
                  (proj₁ $ kanji {x} $ Muvgau a b c d))
  muvduzilcmi x a b c d = sym $ begin
    𝓁 (proj₁ K) ≡⟨ {!!} ⟩
    length x'₁ ℕ.+ length x'₂ ℕ.+ length x'₃ ≡⟨ {!!} ⟩
    𝓁 x ∎
    where
    K = kanji {x} $ Muvgau a b c d
    𝓁 = length ∘ Buffer.lerpinste
    x' = Buffer.lerpinste x
    x'₁ = 𝔽.toℕ a ↑ x'
    x'₂ = ℕ.suc (𝔽.toℕ b) ↓ x'
    x'₃ = 𝔽.toℕ a ↓_ $ ℕ.suc (𝔽.toℕ b) ↑ x'
    open ≡-Reasoning

  muvipas : (x : Buffer)
          → (a b c : Buffer.F x)
          → (d : a 𝔽.≤ b)
          → ((_≡_ on_ $ 𝔽.toℕ a ↑_ ∘ Buffer.lerpinste)
              x
              (proj₁ $ kanji {x} $ Muvgau a b c d))
  muvipas x a b c d = sym $ begin
    T (BL x') ≡⟨ DLP.take++drop (𝔽.toℕ a) (BL x') ▹ sym ▹ cong T ⟩
    T (T (BL x') ++ D (BL x')) ≡⟨ refl ⟩
    _ ≡⟨ teikteik _ _ ▹ cong (T ∘ (_++ D (BL x'))) ⟩
    T (T (BL x) ++ D (BL x')) ≡⟨ teikteik (BL x) a ⟩
    T (BL x) ∎
    where
    T = 𝔽.toℕ a ↑_
    D = 𝔽.toℕ a ↓_
    BL = Buffer.lerpinste
    x' = proj₁ $ kanji {x} $ Muvgau a b c d
    open ≡-Reasoning
    teikteik : ∀ {a} → {A : Set a}
             → (x : List A)
             → {z : List A}
             → (n : Fin $ length x)
             → let n' = 𝔽.toℕ n in
               n' ↑ (n' ↑ x ++ z) ≡ n' ↑ x
    teikteik (_ ∷ _) 𝔽.zero = refl
    teikteik (x ∷ xs) (𝔽.suc n) = teikteik xs n ▹ cong (x ∷_)

  muvisez : (x : Buffer)
          → (a b c : Buffer.F x)
          → (d : a 𝔽.≤ b)
          → let n = ℕ.suc (𝔽.toℕ b ℕ.∸ 𝔽.toℕ a) in
            let x' = proj₁ $ kanji {x} $ Muvgau a b c d in
            (_≡_
              (n ↑_ $ 𝔽.toℕ a ↓_ $ Buffer.lerpinste x)
              (n ↑_ $ 𝔽.toℕ c ↓_ $ Buffer.lerpinste x'))
  muvisez x a b c d = begin
    n ↑ (a' ↓ BLT x) ≡⟨ {!!} ⟩
    n ↑ (c' ↓ BLT x') ∎
    where
    a' = 𝔽.toℕ a
    b' = 𝔽.toℕ b
    c' = 𝔽.toℕ c
    n = ℕ.suc $ b' ℕ.∸ a'
    x' = proj₁ $ kanji {x} $ Muvgau a b c d
    BLT = Buffer.lerpinste
    open ≡-Reasoning

  muviros : (x : Buffer)
          → (a b c : Buffer.F x)
          → (d : a 𝔽.≤ b)
          → let x₂ = proj₂ $ kanji {x} $ Muvgau a b c d in
            (_≡_
              ((𝔽.toℕ b) ↓ Buffer.lerpinste x)
              {!!})
  muviros = {!!}

  muvivimcus : (x : Buffer)
             → (a b c : Buffer.F x)
             → (d : a 𝔽.≤ b)
             → let n = ℕ.suc (𝔽.toℕ b ℕ.∸ 𝔽.toℕ a) in
               let x' = proj₁ $ kanji {x} $ Muvgau a b c d in
               let L = Buffer.lerpinste in
               (_≡_
                 (𝔽.toℕ a ↑ L x ++ ℕ.suc (𝔽.toℕ b) ↓ L x)
                 (𝔽.toℕ c ↑ L x' ++ n ↓ L x'))
  muvivimcus = {!!}

  muvdusin : (x : Buffer)
           → (a b : Buffer.F x)
           → let R = DFP.≤-reflexive refl in
             let K = kanji {x} $ Muvgau a a b R in
             Data.Maybe.Is-nothing (proj₂ K)
           × let x' = proj₁ K in
             let L = Buffer.lerpinste in
             let e = muvduzilcmi x a a b R in
             L x ! a ≡ L x' ! mink a e
           × (_≡_ on ((𝔽.toℕ a ℕ.⊓ 𝔽.toℕ b) ↑_ ∘ L)) x x'
           × (_≡_ on ((𝔽.toℕ a ℕ.⊔ 𝔽.toℕ b) ↑_ ∘ L)) x x'
  muvdusin = {!!}

  xrutis : (x : Buffer)
         → (n : Fin $ length $ Buffer.citri x)
         → (_≡_
             (kanji {x} $ Xruti n)
             (let x' = Buffer.citri x ! n in
              (_,_
                record x {
                  lerpinste = proj₁ x';
                  cablerpinsle = proj₂ x';
                  citri = {!!}}
                nothing)))
  xrutis = {!!}
\end{code}

\chapter{le skami co'e}

\section{la'oi .\F{main}.}
ni'o zabna ciksi la'oi .\F{main}.\ fo ma bau la .lojban.

\begin{code}
{-# NON_TERMINATING #-}
main : Main
main = run $ IO.lift snurytcati IO.>> getArgs IO.>>= uic ∘ 𝕃.head
  where
  postulate snurytcati : ABIO.IO ABU.⊤
  {-# FOREIGN GHC import System.OpenBSD.Plegg #-}
  {-# COMPILE GHC snurytcati = plegg [RPath, WPath, Stdio] #-}
  uic : Maybe String → IO ⊤
  uic = ⟲ <=<ᵢₒ maybe mkDef (IO.pure def)
    where
    _<=<ᵢₒ_ : ∀ {a}
            → {A B C : Set a}
            → (B → IO C)
            → (A → IO B)
            → A
            → IO C
    _<=<ᵢₒ_ g = _∘_ $ IO._>>= g
    def = record {
      datnyveicme = nothing;
      lerpinste = "" ∷ List.[];
      cablerpinsle = 𝔽.zero;
      citri = List.[];
      rejgaudatni = nothing
      }
    mkDef : _
    mkDef c = uit ∘ 𝕊.lines IO.<$> readFile c
      where
      uit : _ → _
      uit [] = record def {datnyveicme = just c}
      uit x@(_ ∷ _) = record {
        datnyveicme = just c;
        lerpinste = x;
        cablerpinsle = 𝔽.opposite 𝔽.zero;
        citri = List.[];
        rejgaudatni = just c
        }
    ⟲ : Buffer → IO ⊤
    ⟲ x = IO.getLine IO.>>= f ∘ reed x
      where
      f : Maybe $ Cmd x → IO ⊤
      f nothing = IO.putStrLn "?" IO.>> ⟲ x
      f (just c) with kanji c
      ... | x' , nothing = ⟲ x'
      ... | x' , just (inj₁ z) = IO.putStrLn z IO.>> ⟲ x'
      ... | x' , just (inj₂ z) with z
      ... | Sisti!ᵢₒ = IO.pure _
      ... | Skamiᵢₒ a = {!!}
      ... | Tciduᵢₒ a b = {!!}
      ... | Rejgauᵢₒ a b = IO.writeFile b a IO.>> ⟲ x
      ... | Sistiᵢₒ = f $ mapₘ (λ _ → Sisti!) $ decToMaybe $ r ≟ c₁
        where
        r = Buffer.rejgaudatni x'
        c₁ = mapₘ (unlines ∘ proj₁) $ 𝕃.head $ Buffer.citri x'
\end{code}
\end{document}
