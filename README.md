# Documentação Técnica: Formalização da Semântica eBPF e Verificação de Programas em Lean 4

## 1. Introdução

Este documento apresenta a formalização da semântica da máquina virtual eBPF (Extended Berkeley Packet Filter) utilizando o assistente de provas Lean 4. O projeto estabelece uma base rigorosa para a verificação formal de programas eBPF, definindo o estado da máquina, o conjunto de instruções, a semântica operacional (*small-step*), e um interpretador executável. Adicionalmente, constrói-se um arcabouço de Lógica de Separação e Lógica de Hoare, culminando em um Gerador de Condições de Verificação (VCG) provado correto (*sound*) para garantir propriedades de segurança em filtros de rede.

---

## 2. Estado de Máquina e Memória

[cite_start]O estado da máquina eBPF é formalizado como o produto cartesiano entre o estado dos registradores e o estado da pilha[cite: 276]. 

* [cite_start]**Registradores (`RegsState`)**: A máquina possui 11 registradores enumerados de $r0$ a $r10$, além de um registrador auxiliar $r\_$[cite: 273, 274]. [cite_start]O estado dos registradores é modelado como uma função total mapeando registradores para números naturais ($Reg \to \mathbb{N}$)[cite: 274].
* **Pilha (`StackState`)**: A memória de pilha possui tamanho fixo de 512 bytes. [cite_start]É modelada como uma função de índices finitos para opções de valores naturais ($Fin\ 512 \to Option\ \mathbb{N}$)[cite: 275].
* [cite_start]**Estado Global (`MachineState`)**: Definido pela tupla $(RegsState \times StackState)$[cite: 276]. [cite_start]Operadores de leitura e escrita explícitos foram formalizados, permitindo a sintaxe abstraída via macros matemáticas, como $s.[index]$ para leitura e $s.[dst \mapsto val]$ para atualização[cite: 283].

---

## 3. Conjunto de Instruções e Sintaxe

[cite_start]A sintaxe abstrata dos programas eBPF é definida de forma algébrica por meio do tipo indutivo `opCode`[cite: 285]. 

* [cite_start]**Aritmética e Lógica**: Operações suportadas incluem adições e conjunções bit a bit, parametrizadas tanto por valores imediatos (ex: `add_K`, `and_K`) quanto por registradores (ex: `add_X`, `and_X`)[cite: 285, 286, 287].
* **Controle de Fluxo**: Instruções de salto condicional avaliam relações de desigualdade (`jgt`), diferença (`jne`), igualdade (`jeq`) e máscara de bits (`jset`). [cite_start]Elas calculam o deslocamento (*offset*) relativo ao Program Counter ($PC$)[cite: 288, 289, 290, 291].
* **Memória e Encerramento**: A manipulação de memória é efetuada por instruções de carregamento dinâmico (`ldh_X`) e armazenamento estático/dinâmico (`sth_K`, `sth_X`). [cite_start]A instrução terminal é designada por `exit`[cite: 296, 297, 298].
* [cite_start]Um programa (`Code`) é estruturado como uma sequência encadeada (`List opCode`)[cite: 298].

---

## 4. Semântica Operacional

A execução de instruções é regida por uma semântica de passos pequenos (*small-step semantics*), formalizada pelo predicado indutivo `step`. [cite_start]Esta relação define as transições de estado $step(code, pc, next\_pc, s, next\_s)$[cite: 299].

* **Regras de Transição**: Para cada construtor em `opCode`, há axiomas correspondentes. [cite_start]Por exemplo, `rule_add_X` define a semântica da adição entre registradores, atualizando o destino e incrementando o $PC$[cite: 306, 307].
* [cite_start]**Ramificação**: Os saltos bifurcam a prova em dois construtores mutuamente excludentes (ex: `jgt_X_true` e `jgt_X_false`), dependendo da avaliação da guarda condicional no estado atual[cite: 322, 324].
* [cite_start]**Fecho Transitivo**: O predicado `run` captura a execução iterada de múltiplos passos, compondo transições elementares de modo indutivo através da construtores `halt` e `seq`[cite: 354, 355, 356].

---

## 5. Interpretador Executável

[cite_start]Em paralelo à semântica relacional, fornece-se uma especificação computável por meio de um interpretador[cite: 414].

* [cite_start]**Avaliação Passo-a-Passo (`step_instr`)**: Uma função pura computa o próximo estado da máquina e o incremento escalar do $PC$ com base na instrução corrente[cite: 396]. 
* **Controle de Terminação (`fuel`)**: Dado o problema da parada, a função `interp` incorpora um contador de combustível ($fuel$) para forçar a terminação de eventuais laços infinitos, retornando `Option MachineState`[cite: 414, 415].
* [cite_start]**Teorema de Correspondência**: O lema `step_instr_to_step` (estabelecido no módulo de correção) formaliza que o comportamento determinístico de `step_instr` reflete rigorosamente a relação axiomatizada em `step`[cite: 1, 2, 3].

---

## 6. Lógica de Separação e Sistema de Tipos de Hoare

A metodologia primária de prova requerida para validar a segurança da memória e a ausência de vazamentos é suportada por Lógica de Separação.

* [cite_start]**Asserções Espaciais (`Assert`)**: Mapeiam o estado da máquina para proposições lógicas ($MachineState \to Prop$)[cite: 360].
* **Conectivos**: A Lógica de Separação introduz o modelo de "separação" de pilhas via predicados como o *Separating Conjunction* ($P * Q$) e o *Magic Wand* ($P -* Q$), requerendo o particionamento do subespaço da memória via `State_disjoint` e `State_union`[cite: 360, 361].
* **Lógica de Hoare (`Triple`)**: As tríplices de Hoare ($\{P\} \ prog \ @\ pc \ \{Q\}$) asseguram a consistência pós-execução. [cite_start]Inferências como `consequence` (fortalecimento de premissa e enfraquecimento de conclusão) e `frame` (extensão local de estado imutável) formam o alicerce matemático[cite: 364, 365]. [cite_start]As regras específicas, tais como `jne_X_true`, integram as bifurcações das lógicas condicionais no ambiente lógico[cite: 379].

---

## 7. Geração de Condições de Verificação (VCG)

O VCG é responsável por automatizar parcialmente o processo de construção de provas lógicas, transformando as instruções do código em fórmulas de primeira ordem.

* **Pré-Condição Mais Fraca (`wp`)**: Transforma inversamente o estado pós-execução. Em operações condicionais (`jgt`, `jne`), ramifica as premissas em proposições conjuntivas baseadas no salto (`Q_jump`) ou queda (`Q_next`)[cite: 20, 27].
* [cite_start]**Tratamento de Laços (`InvMap`)**: O mapeamento `inv` acomoda variantes lógicas e invariantes essenciais na resolução contínua do $PC$, contornando limites recursivos[cite: 39, 43].
* **Teoremas de Solidez (*Soundness*)**:
    * [cite_start]`wp_sound`: Garante que a Pré-Condição Mais Fraca gera uma tríplice de Hoare válida perante os saltos e transições estruturais[cite: 88, 97].
    * [cite_start]`vcg_sound`: O teorema principal estabelece formalmente que se um bloco for validado perante suas condições laterais (via gerador de VCG parametrizado por limites recursivos), a sua execução sob a pré-condição declarada atinge de fato o seu objetivo sem refutações operacionais[cite: 201, 202].
    * [cite_start]`hoare_step_sound`: Demostra a compatibilidade em uma única transição de instrução perante mutação de estado isolada (`step_locality`)[cite: 203, 204].

---

## 8. Aplicações e Casos de Estudo

Para validar a integridade semântica da abstração, programas focados no modelo de filtragem de pacotes clássico foram definidos e formalmente provados corretos usando as táticas customizadas de VCG.

* [cite_start]**Filtro ARP Limitado (`prog_only_arp`)**: Comprova formalmente o aceite lógico exclusivamente de pacotes marcados com *ethertype* ARP ($0x0806$), setando a flag $r0 = 1$ para tráfego válido e dropando conexões espúrias[cite: 247, 248].
* **Identificação de Tráfego de Sub-rede (`prog_subnet`)**: O sistema foi atestado frente ao parse e aritmética bit a bit para descarte de acessos fora do intervalo de máscara exigido, assegurando isolamento do *payload* provido nas pilhas de índices arbitrários[cite: 258, 259, 260].
* **Filtro IPv4 TCP SSH (`prog_only_IPv4_TCP_SSH`)**: Um modelo complexo garantindo que *headers* IP validam precisamente a correspondência para porta SSH ($0x16$), verificando bytes disjuntos sequenciais e submetendo a demonstração pelas rotinas sintáticas do `vcg_sound`[cite: 264, 267, 268].