import Mathlib.Data.Nat.Defs
import Aesop



-- Comando para definir o tamanho maximo da arvore de recursão


/-
Separar em decode e encode
  Não será necessario para o meu trabalho
  Em x86 precisa pois as instruçoes fazem parte da memoria
  Decode lê memória de endereço i e tenta produzir uma instrução ι
  Definir o Step: s → s , que vai ser o decode+encode
  step : S ⇀ S que faz um pequeno passo
  decodifica a instrução apontada pelo PC/EIP
  aplica a execução da instrução (ou é indefinida em caso de falha)
Composição repetida define run(k,s) — o estado após k passos (se todos bem-sucedidos).
O run(k,s) executa k passos sobre s
Quando o Step é indefinido ocorre a falha

Estado da maquina S = (Pilha, registradores)
  Trabalha com um estado Parcial Σ
  Σ = (reg ⇀ DWORD) × (flag ⇀ {true,false,undef}) × (DWORD ⇀ (BYTE ∪ {unmapped}))
Separa as instruçoes em outro conjunto
Operador ], que faz a união de dominios disjuntos, que faz de (Σ, ]) uma logica de separação
Assertions são então predicados sobre Σ
  "r 7_ v" significa “no fragmento considerado, o registador r tem valor v”.
  i..j 7→ ι significa “a memória entre i e j contém os bytes que decodificam para a instrução ι”


Como Cpu não terminha, usa a premissa Safe
  Que determina que é possivel executar k passos sobre a maquina
  “a partir de um estado onde P vale, executar k passos é seguro (não falha)”.
  Isso é continuation-passing style (CPS)
  porque a especificação não afirma que um postcondition Q ocorrerá;
  antes, Q é vista como uma continuação:
  “se mais à frente for verdade que Q, então antes precisávamos de P”

A lógica de especificação (tipo spec)
  Spec — uma especificação S é um conjunto de pares (k,P)
  fechado para dois comportamentos:
  (i) fechado sob k′ ≤ k (se vale para k então vale para menos passos)
  (ii) fechado sob extensão por frames:
  se (k,P) ∈ S então para qualquer R também (k, P * R) ∈ S.
  Ou seja, S descreve “o que precisa valer no footprint relevante” e
  permite qualquer invariância extra R que estejamos a carregar.

Connectivos chave
  S ⊗ R (frame connective)
    o conjunto de (k,P) tais que (k, P * R) ∈ S. Interpretação:
    “S funcionando num contexto que também possui o invariante R”.
    Isto permite provar regras de frame de ordem superior.

  S θ R (read-only frame) exigência mais forte:
    S só é admitido se preservar exactamente R
    (pode quebrar temporariamente, mas deve restaurar R).
    Formalmente S θ R ≜ ∀σ ∈ R. S ⊗ {σ}.
    Útil para invariantes do tipo
    “essa região da memória não pode ser modificada no final”.

  .S (later / depois)
    desloca os índices de passo:
    (k,P) ∈ .S significa que para todos k′ < k temos (k′,P) ∈ S.
    Serve para fazer indução.

{P} c {Q} ≜ ∀i,j. (
    safe ⊗ (EIP 7_ j ∗ Q) ⇒
    safe ⊗ (EIP 7_ i ∗ P) ) θ i..j 7→ c
  EIP é o pc do programa, e aponta para a proxima instrução
  para todo par de endereços i..j que correspondam ao bloco c,
  se — quando estivermos na posição j com Q e um frame —
  executarmos com segurança, então antes, na posição i com P e o mesmo frame,
  também seremos seguros. Assim o post-condição Q aparece como uma continuação;

-/



/-
Como acho que ficaria o organização do ebpf

O estado da maquina iria ser representado apenas pelas memorias
  (Pilha, Registradores e PC)
  E validar o estado da maquina foi feito por meio da clausula "Safe" no trabalho

O "programa" seria na realidade uma sequencia de "c" da tripla de hoare
  {P} c {Q}
  As possiveis transformaçoes sobre o estado da maquina
  O trabalho utilizou a logica do step para definir esse C
  Ele usa a noção tambem de "footprint":
  Que seria um subconjunto da memoria que foi alterado por algo
  Porque usar estado parcial seria logica de separação?

Um Assertion é um predicado sobre um estado parcial


Iria usar a mesma logica de K operaçoes sobre os estados, para "executar" o programa
e conseguir provar por indução sobre as intruçoes
  Se eu provar separadamente para cada instrução sobre o estado S
  Estou provando para sucessivas aplicações sobre um estado S

?Verification condition generator


Desenvolver o exemplo/exercicios do Livro

Semantica do IPV4


-/




--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
-- Início da semantica do Ebpf

-- Estado: mapeia variáveis para números
-- Dada uma String eu retorno um numero qualquer
def State := String → ℕ

/- Atualização de estado
Estou criando uma função anonima que tem a seguinte estrutura
Ela recebe um y que é uma string

Caso a string y seja igual a string X retorno o meu numeral
que anteriormente já foi um caso falso do meu if
caso falso que criou/anexou um novo estado s com a string y acoplada
estado s que agora vai ser verdadeiro e permitir anexar n a y
-/
def update (s : State) (x : String) (n : ℕ) : State :=
  fun y => if y = x then n else s y
/-
fun é do tipo String → ℕ, o mesmo tipo de String
y é uma string, recebida como parametro
e "if y = x then n else s y" é do tipo ℕ
logo fun y => if y = x then n else s y é do tipo
String → ℕ ou State
-/
def s_test : State :=
  fun v => if v == "x" then 10
           else if v == "y" then 5
           else if v == "z" then 15
           else 0

def s1_test := update s_test "x" 99

#eval s_test "x" -- 10
#eval s1_test "x" -- 99
#eval s_test "a" -- 0
-- s1_test é o novo estado apos realizar update no x
def s2_test := update s_test "a" 23
#eval s2_test "a" -- 0
/-
 s2_test é o novo estado apos realizar update no a
o adicionando ao state S2, já que o state é uma função do tipo
s → ℕ, a função update cai no caso else, adicionando a como uma string
e posteriormente cai no caso verdadeiro, adicionando 23
-/

def s_emp : State :=
 fun _x => 0

#check s_emp

def s1_emp := update s_test "x" 98

def readState (s : State) : ℕ :=
  s "x"

#check readState
#eval readState s1_emp

#eval s1_emp "x" -- 98
#check (s1_emp )

/-
Linguagem de Statements:
skip         : não altera o estado
assign x y   :  avalia o estado y e armazena em x
  gerando um novo statement
seq s1 s2    : executa s1 seguido de s2
  executa um statement e em seguida um outro statement
ifThenElse c s1 s2   : condicional
  avalia um estado c que armazena um prop
  escolhe entre dois statements S1 ou S2 para executar
  e executa/retorna um deles
whileDo c S1      : laço
  avalia um estado c que armazena um prop
  e executa um statement S1 caso seja verdadeiro
-/

inductive Stmt where
  | skip : Stmt
  | assign : String → (State → ℕ) → Stmt
  | seq : Stmt → Stmt → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo : (State → Prop) → Stmt → Stmt

/- Semântica big-step
recebe um comando c e dois estados s1 e s2 e retorna um prop



-/
inductive big_step : Stmt → State → State → Prop where
/-
recebe comando _c_ igual a Stmt.skip
e dois estados _s_ que serão iguais
a regra de diz que os dois estados s devem ser iguais
por isso o retorno é um prop
pois se tivermos Stmt.skip s_1 s_2 isso seria incorreto
pois a propia definicação de big_step Stmt.skip
fala que os estados devem ser os mesmos
-/
  | skip_rule (s : State) :
      big_step Stmt.skip s s
/-
recebe um comando _c_ do formato Stmt.assign x a
que carrega junto ao comando um
_x_ que é uma string e um _a_ que é um estado

recebe tambem o estado _s_, que é o estado a ser atualizado

e recebe tambem um segundo estado que vai ter o formato
update do estado _s_ que foi recebido como entrada
sobre a string _x_ que é o "nome" da minha variavel
com o valor de (a s), que é
o resultado de avaliar a expressão _a_ sobre o estado _s_
produzindo um natural que sera armazenado em _x_
atualizando o estado anterior
-/
  | assign_rule (s : State) (x : String) (a : State → ℕ) :
      big_step (Stmt.assign x a) s (update s x (a s))
/-
a regra de sequencia recebe dois comandos e tres estados

O primeiro passo é definir H1
que vai ser chamar bigStep para o primeiro comando recebido
sobre um estado s que deve produzir um estado s1

em seguida definimos H2
que vai ser chamar bigStep para o segundo comando recebido
sobre o estado _s1_ que deve produzir um estado _t_
sendo estado _t_ o resultado de executar dois comandos seguidos
sobre o estado _s_
-/
  | seq_rule (S₁ S₂ : Stmt) (s s₁ t : State)
      (h₁ : big_step S₁ s s₁)
      (h₂ : big_step S₂ s₁ t) :
      big_step (Stmt.seq S₁ S₂) s t
/-
A regra recebe inicialmente um _b_, que espera um estado para retornar um Prop
e dois comandos, S₁ e S₂

_Hb_ é a minha hipotese para avaliar o caso verdadeiro
se _b_ sobre o estado _s_ for verdadeiro
eu "executo" _h_ que é chamar a função bigstep
para o comando S1 sobre o estado _s_, gerando _t_

-/
  | if_true_rule (B : State → Prop) (S₁ S₂ : Stmt)
      (s t : State)
      (hB : B s)
      (h : big_step S₁ s t) :
      big_step (Stmt.ifThenElse B S₁ S₂) s t
/-
mesma estrutura geral do caso anterior

apenas com a mudança de que meu h possui a negação
e devido a isso eu avalio o comando S₂
-/
  | if_false_rule (B : State → Prop) (S₁ S₂ : Stmt)
      (s t : State)
      (hB : ¬ B s)
      (h : big_step S₂ s t) :
      big_step (Stmt.ifThenElse B S₁ S₂) s t
/-
A regra recebe inicialmente um _b_, que espera um estado para retornar um Prop
e um comando S, e estados s s₁ e t

_H₁_ é a minha hipotese para avaliar o caso verdadeiro
se _b_ sobre o estado _s_ for verdadeiro
eu "executo" _h₁_ que é chamar a função bigstep
para o comando S sobre o estado _s_, gerando _s₁_

_H₂_ é a minha hipotese para avaliar o proximo passo
Eu chamo bigStep passando como comando inicial
um while com a condição B sobre o comando S e estado s₁
resultando em t, resumundo
Executo o comando S sobre s, gerando s₁, e logo em seguida
chamo "recursivaente" para o proximo passo, executando S para s₁
gerando o meu t
-/
  | while_true_rule (B : State → Prop) (S : Stmt)
      (s s₁ t : State)
      (hB : B s)
      (h₁ : big_step S s s₁)
      (h₂ : big_step (Stmt.whileDo B S) s₁ t) :
      big_step (Stmt.whileDo B S) s t
/-

Uma "continuação" regra anterior, que seria o meu caso base
de uma função recursiva

A regra recebe inicialmente um _b_, que espera um estado para retornar um Prop
, um comando S e um estado s

_Hb_ é a minha hipotese para avaliar o caso falso
se _b_ sobre o estado _s_ for falso
o estado gerado pelo while é o mesmo que foi recebido

-/
  | while_false_rule (B : State → Prop) (S : Stmt)
      (s : State)
      (hB : ¬ B s) :
      big_step (Stmt.whileDo B S) s s

/-
------------------------------------------------------------------------------
  AÇUCAR SINTÁTICO PARA SEQUÊNCIAS
------------------------------------------------------------------------------
-/

-- Permite escrever S₁; S₂ em vez de (Stmt.seq S₁ S₂)
infixr:90 "; " => Stmt.seq


-- Versão alternativa nomeada (se quiser)
def PartialHoare (P : State → Prop)
    (S : Stmt)
    (Q : State → Prop) : Prop :=
  ∀ s t, P s → big_step S s t → Q t

-- Macro para usar a notação tradicional de Hoare:
-- Exemplo:  {* P *} (S) {* Q *}
macro "{*" P:term " *} " "(" S:term ")" " {* " Q:term " *}" : term =>
  `(PartialHoare $P $S $Q)

-- Definição da macro para atualização de estado
macro s:term "[" name:term "↦" val:term "]" : term =>
  `(update $s $name $val)

/-
------------------------------------------------------------------------------
  REGRAS DA LÓGICA DE HOARE
------------------------------------------------------------------------------
Cada teorema representa uma das regras clássicas da lógica de Hoare.
Por enquanto, todos estão com `sorry` (provas omitidas).
------------------------------------------------------------------------------
-/

-- Regra Skip: {P} skip {P}
-- Executar "skip" mantém o estado inalterado, logo P continua valendo.
theorem skip_intro {P : State → Prop} :
  {* P *} (Stmt.skip) {* P *} := by
  intros S₁ -- Suponho um estado S₁
  intros S₂ -- Suponho um estado S₂
  intros h1 -- Suponho que P aplicado a S₁ é verdade
  intros h2 -- Suponho que Skip de S₁ retorna S₂
  --Agora tenho que Prova S₂
  cases h2
  -- Aplico a hipotese que Skip de S1 gera  S₂
  -- Ai tenho que provar P S₁
  exact h1 -- P S₁ foi uma hipotese que obtive no inicio


-- Regra Assign: {Q[a/x]} x := a {Q}
-- Substitui x por a na pós-condição.
theorem assign_intro (P) {x a} :
  {* fun s ↦ P (s [ x ↦ a s]) *}
  (Stmt.assign x a)
  {* P *} := by
  intros S₁ -- Suponho um estado S₁
  intros S₂ -- Suponho um estado S₂
  intros h₁ -- Suponho que P aplicado a:
  --  atualizar o estado S1, na variavel x sobre o valor
  -- retornado por encontrar a em S₁ é verdade
  intros h₂ -- SUponho que atribuir o valor a para a variavel x
  --sobre o estado S₁ gera o estado S₂
  cases h₂ --aplico a hipotese que atribuir o valor a encontrado
  -- em S₁ sobre a variavel x gera S₂
  -- Ai resta provar que é possivel encontrar o valor de a em S₁
  -- e é possivel dar update de S₁ sobre a variavel x
  -- com o valor de a que foi encontrado tambem em S₁
  -- pois update S₁ x (a S₁) gera S₂
  exact h₁ -- update S₁ x (a S₁) é uma hipote se obtive no inicio

-- Regra de Sequência:
-- {P} S {Q}, {Q} T {R}  ⇒  {P} S;T {R}
theorem seq_intro {P Q R S T}
  (hS : {* P *} (S) {* Q *})
  (hT : {* Q *} (T) {* R *}) :
  {* P *} (S; T) {* R *} := by
  intro S₁ -- Suponho um estado S₁
  intro S₂ -- Suponho um estado S₂
  intro h₁ -- Suponho que P aplicado é S₁ é verdade
  intro h₂ -- Suponho que aplicar a sequencia a S₁ gera S₂
  cases h₂ with -- aplico a hipotese h2 que a sequencia de S₁ é verdade
  -- A sequencia tem a seguinte cara
  -- Aplicar S sobre P gera Q
  -- Aplicar T sobre Q gera R
  -- A regra pode ser lida "ao contrario" tambem
  -- e tenho que provar duas coisas
  -- S sobre P gera Q e T sobre Q gera R
  | seq_rule _ _ _ S_Mid _ hS' hT' =>
    apply hT -- Aplico a regra que diz que T sobre Q gera R
    -- E ganho as seguintes hipoteses
    -- um estado intermediario S_Mid
    -- a hipotese que aplicar Step S sobre S₁ gera S_Mid
    -- e a hipotese que aplicar T sobre S_Mid gera S₂
    { -- Aqui tenho que provar que o estado intermediario Q é valido
      apply hS
      -- Para isso, aplico hS, que diz que aplicar S sobre P gera Q
      -- agora tenho que provar P
      -- E que eu consigo aplicar S sobre um estado '
      {
        exact h₁ -- Tenho como hipotese que P sobre S₁ é valido
      }
      {
        exact hS'-- tenho como hipose que aplicar S sobre S₁ gera outro estado
      }
    }
    {
      -- Ai falta provar a segunda parte do caminho
      -- que aplicar T sobre o estado intermediario gera um estado S₂
      exact hT'
      -- Isso é exatamente a hipote hT' que eu ganhei pela regra da sequencia
    }


-- Regra If:
-- {P ∧ B} S {Q}, {P ∧ ¬B} T {Q} ⇒ {P} if B then S else T {Q}
theorem if_intro {B P Q S T}
  (hS : {* fun s ↦ P s ∧ B s *} (S) {* Q *})
  (hT : {* fun s ↦ P s ∧ ¬ B s *} (T) {* Q *}) :
  {* P *} (Stmt.ifThenElse B S T) {* Q *} := by
  intro S₁ -- Suponho um estado S₁
  intro S₂ -- Suponho um estado S₂
  intro h₁ -- Suponho que P aplicado é S₁ é verdade
  intro h₂ -- Suponho que aplicar o If a S₁ gera S₂
  -- Agora tenho que provar que Q sobre o estado S₂ é valido
  cases h₂ with -- Aplico a hipotese h₂, que define a regra
  -- para ter que provar S₁ em vez de S₂
  -- onde são avaliados dois casos se for verdadeiro ou falso
  -- pois h₂ é uma regra IF
  | if_false_rule _ _ _ _ _ hB hT' =>
    apply hT -- para o caso falso tenho que provar que
    -- a condição é falsa e que P sobre s é um estado valido
    exact And.intro h₁ hB
    -- separo o ∧ em duas partes
    -- a primeira fala que P sobre um estado s é valido
    -- isso é igual a hipotese h1 == P S₁
    -- a segunda parte fala que condição é falsa
    -- hipotese que ganhei pelo construtor da regra
    exact hT'
    -- ai como ja foi provado que a condição é falsa
    -- e P pode gerar um estado S₁
    -- resta apenas provar que aplicar T sobre s₁ gera S₂
    -- hipotese que ganhei pelo construtor da regra
  | if_true_rule _ _ _ _ _ hB hS' =>
    apply hS -- para o caso veraddeiro tenho que provar que
    -- a condição é veraddeira e que P sobre s é um estado valido
    exact And.intro h₁ hB
    -- separo o ∧ em duas partes
    -- a primeira fala que P sobre um estado s é valido
    -- isso é igual a hipotese h1 == P S₁
    -- a segunda parte fala que condição é verdadeira
    -- hipotese que ganhei pelo construtor da regra para o caso Falso
    exact hS'
    -- ai como ja foi provado que a condição é verdadeira
    -- e P pode gerar um estado S₁
    -- resta apenas provar que aplicar S sobre s₁ gera S₂
    -- hipotese que ganhei pelo construtor da regra para o caso verdadeiro

-- Regra While:
-- {P ∧ B} S {P} ⇒ {P} while B do S {P ∧ ¬B}
-- P é o invariante de laço.
/-
theorem while_intro1 (P) {B S}
  (h : {* fun s ↦ P s ∧ B s *} (S) {* P *}) :
  {* P *} (Stmt.whileDo B S) {* fun s ↦ P s ∧ ¬ B s *} := by
  intro s t hs hst
  generalize ws_eq : (Stmt.whileDo B S, s) = Ss
  rw [ws_eq] at hst
  induction hst generalizing s with
  | skip s'                       => cases ws_eq
  | assign x a s'                 => cases ws_eq
  | seq S T s' t' u hS hT ih      => cases ws_eq
  | if_true B S T s' t' hB hS ih  => cases ws_eq
  | if_false B S T s' t' hB hT ih => cases ws_eq
  | while_true B' S' s' t' u hB' hS hw ih_hS ih_hw =>
    cases ws_eq
    apply ih_hw
    { apply h
      { apply And.intro <;>
          assumption }
      { exact hS } }
    { rfl }
  | while_false B' S' s' hB'      =>
    cases ws_eq
    aesop
-/

theorem while_intro (P) {B S}
  (h : {* fun s ↦ P s ∧ B s *} (S) {* P *}) :
  {* P *} (Stmt.whileDo B S) {* fun s ↦ P s ∧ ¬ B s *} := by
  intro S₁ -- Suponho um estado S₁
  intro S₂ -- Suponho um estado S₂
  intro h₁ -- Suponho que P aplicado é S₁ é verdade
  intro h₂ -- Suponho que aplicar a regra while
  -- Sobre uma condição B
  -- com um estado S₁ gera S₂
  -- me resta provar que P S₂ é valido
  -- E que a condição é falsa em algum estado S₂
  -- Ou seja, que a função termina
  generalize ws_eq : (Stmt.whileDo B S, S₁) = Ss
  --rw [ws_eq] at h₂
  cases h₂ with
  -- Separo em dois casos, para a regra falsa e verdadeira
  | while_true_rule _ _ _ S_Mid T hB h' hs'=>
  apply And.intro
  {
    -- para a regra verdadeira eu tenho que provar que P S₂ é valido
    apply h
    exact And.intro h₁ hB
    sorry
  }
  {


    sorry
  }
  | while_false_rule  S₄ hB h' hs' =>
  -- Para o caso falso tenho que provar duas coisas
  -- que P para o estado S₁ é valido
  -- e que a condição é falsa
  -- onde P S₁ é a primeira hipotese que ganhei
  -- E a condição falsa surge da regra
  exact And.intro h₁ hs'

-- Regra de Consequência (geral):
-- P' → P, {P} S {Q}, Q → Q' ⇒ {P'} S {Q'}
theorem consequence {P P' Q Q' S}
  (h : {* P *} (S) {* Q *})
  (hp : ∀s, P' s → P s)
  (hq : ∀s, Q s → Q' s) :
  {* P' *} (S) {* Q' *} := by
  intro S₁ -- Suponho um estado S₁
  intro S₂ -- Suponho um estado S₂
  intro h₁ -- Suponho que P aplicado é S₁ é verdade
  intro h₂ -- Suponho que o estado S₁ deriva a partir de S para S₂
  apply hq
  sorry

-- Versões simplificadas das regras de consequência (apenas à esquerda ou à direita).
theorem consequence_left (P') {P Q S}
  (h : {* P *} (S) {* Q *})
  (hp : ∀s, P' s → P s) :
  {* P' *} (S) {* Q *} := by


  sorry

theorem consequence_right (Q) {Q' P S}
  (h : {* P *} (S) {* Q *})
  (hq : ∀s, Q s → Q' s) :
  {* P *} (S) {* Q' *} := by

  sorry

-- Variante da regra Skip com pós-condição diferente: {P} skip {Q}, se P → Q.
theorem skip_intro' {P Q} (h : ∀s, P s → Q s) :
  {* P *} (Stmt.skip) {* Q *} := by
  intro S₁ -- Suponho um estado S₁
  intro S₂ -- Suponho um estado S₂
  intro h₁ -- Suponho que P aplicado é S₁ é verdade
  intro h₂
  sorry

-- Variante da regra Assign com pós-condição explícita: {P} x := a {Q}, se P → Q[a/x].
theorem assign_intro' {P Q x a}
  (h : ∀s, P s → Q (s[x ↦ a s])) :
  {* P *} (Stmt.assign x a) {* Q *} :=

  sorry

-- Variante de sequência invertida na ordem dos parâmetros.
theorem seq_intro' {P Q R S T}
  (hT : {* Q *} (T) {* R *})
  (hS : {* P *} (S) {* Q *}) :
  {* P *} (S; T) {* R *} := by
  apply seq_intro hS hT

-- Variante estendida da regra While com invariante explícito I.
theorem while_intro' {B P Q S} (I)
  (hS : {* fun s ↦ I s ∧ B s *} (S) {* I *})
  (hP : ∀s, P s → I s)
  (hQ : ∀s, ¬ B s → I s → Q s) :
  {* P *} (Stmt.whileDo B S) {* Q *} := by
  intro S₁ -- Suponho um estado S₁
  intro S₂ -- Suponho um estado S₂
  intro h₁ -- Suponho que P aplicado é S₁ é verdade
  intro h₂
  sorry

-- Regra Assign (forma forward): define a pós-condição em termos de estados anteriores.
theorem assign_intro_forward (P) {x a} :
  {* P *} (Stmt.assign x a)
  {* fun s ↦ ∃n0, P (s[x ↦ n0]) ∧ s x = a (s[x ↦ n0]) *} := by
  intro S₁ -- Suponho um estado S₁
  intro S₂ -- Suponho um estado S₂
  intro h₁ -- Suponho que P aplicado é S₁ é verdade
  intro h₂
  sorry

-- Regra Assign (forma backward): define a pré-condição em termos de estados posteriores.
theorem assign_intro_backward (Q) {x a} :
  {* fun s ↦ ∃n', Q (s[x ↦ n']) ∧ n' = a s *}
  (Stmt.assign x a) {* Q *} := by
  intro S₁ -- Suponho um estado S₁
  intro S₂ -- Suponho um estado S₂
  intro h₁ -- Suponho que P aplicado é S₁ é verdade
  intro h₂
  sorry



/-
Mudanças implementação
Fugir o maximo possivel de multiplos campos
Focar nas operações que estão no bpf-Linux

Fazer uma pequena especificação Lean
Fazer semantica do eBPF usando a logica de Hoare


-/
