# Documentação Técnica: Formalização e Verificação do eBPF em Lean 4

## 1. Introdução e Visão Geral
Este projeto apresenta uma formalização completa e rigorosa da semântica da eBPF (*Extended Berkeley Packet Filter*) utilizando o assistente de provas Lean 4. O objetivo é fornecer uma base matemática para a verificação formal de programas eBPF, garantindo propriedades de segurança e correção funcional através de Lógica de Hoare e Lógica de Separação.

A arquitetura do projeto divide-se em:
- **Modelo de Dados**: Definição de estados, registradores e memória.
- **Semântica Operacional**: Regras de transição de pequenos passos (*small-step*) e execução.
- **Interpretador**: Uma implementação executável para simulação.
- **Lógica de Verificação**: Implementação de tríplices de Hoare e um Gerador de Condições de Verificação (VCG).
- **Provas de Soundness**: Demonstração de que o VCG e a lógica de Hoare respeitam a semântica operacional.

---

## 2. Arquitetura da Máquina e Memória (`A_Memory.lean`)
O estado da máquina (`MachineState`) é composto por dois elementos principais:
- **Registradores (`RegsState`)**: Uma função `Reg → ℕ` que mapeia os registradores `r0` a `r10` para valores naturais. O registrador `r_` é tratado como um registrador nulo (sempre retorna 0).
- **Pilha (`StackState`)**: Uma memória de 512 bytes modelada como `Fin 512 → Option ℕ`. O uso de `Option` permite representar células de memória não inicializadas.

As operações de leitura e escrita são abstraídas por macros:
- `s.(r)`: Leitura do registrador `r`.
- `s.[dst ↦ val]`: Atualização do registrador `dst`.
- `s.[idx]`: Leitura da pilha na posição `idx`.
- `s.[idx] := val`: Escrita na pilha.

---

## 3. Conjunto de Instruções (`B_Instructions.lean`)
As instruções eBPF são definidas no tipo indutivo `opCode`. O conjunto suportado inclui:
- **Aritmética**: `add_K` (imediato), `add_X` (registrador), `and_K`, `and_X`.
- **Movimentação**: `mov_K`, `mov_X`.
- **Saltos Condicionais**: `jgt` (maior que), `jne` (diferente), `jeq` (igual), `jset` (bitmask).
- **Memória**: `ldh_X` (load half-word), `sth_K` (store imediato), `sth_X` (store registrador).
- **Controle**: `exit` para encerrar a execução.

---

## 4. Semântica Operacional (`C_Semantic_Step.lean`)
A semântica é definida através de relações indutivas:
- **`step`**: Define a transição de um único passo entre estados (`PC → PC → MachineState → MachineState`). Cada instrução possui uma regra específica (ex: `rule_mov_X`, `rule_ldh_X`).
- **`run`**: O fecho transitivo da relação `step`. Define quando um programa termina (`halt`) ou continua (`seq`).
- **`runV2`**: Uma variante de execução simplificada para provas de composição.

---

## 5. Interpretador e Simulação (`E_Interpreter.lean`)
O arquivo `E_Interpreter.lean` fornece uma versão computável da semântica:
- **`step_instr`**: Uma função que recebe uma instrução e o estado atual, retornando o novo estado e o deslocamento do Program Counter.
- **`interp`**: Função recursiva que executa o código. Utiliza um parâmetro `fuel` (combustível) para garantir a terminação em Lean, permitindo a execução de programas eBPF em tempo de compilação ou via `#eval`.

---

## 6. Lógica de Hoare e Separação (`D_Sep_Logic.lean`)
Para provar propriedades de programas, o projeto implementa uma lógica de prova baseada em asserções (`Assert`):
- **Conectivos de Separação**: `P ∗ Q` (conjunção separadora) e `P -∗ Q` (magic wand) permitem raciocinar sobre partes disjuntas da memória.
- **Tríplices de Hoare (`Triple`)**: A estrutura `⦃P⦄ prog @ pc ⦃Q⦄` afirma que, se a pré-condição `P` for satisfeita, a execução do programa a partir de `pc` resultará num estado que satisfaz a pós-condição `Q`.
- **Regras de Inferência**: Inclui regras para todas as instruções eBPF, além de regras estruturais como `consequence`, `frame` e `disj`.

---

## 7. Geração de Condições de Verificação (`G_Ver_Cond_Gen.lean`)
O VCG automatiza a criação de provas:
- **`wp` (Weakest Precondition)**: Calcula a pré-condição mais fraca para uma única instrução. Para saltos, a função gera condições que cobrem tanto o caminho do salto quanto o caminho sequencial.
- **`vcg`**: Função recursiva que percorre o código (usando `fuel`) e gera uma estrutura `VCGResult` contendo a pré-condição calculada e uma lista de condições de verificação (VCs - obrigações de prova).
- **`inv` (Invariants)**: Suporta o uso de mapas de invariantes para lidar com laços ou saltos complexos.

---

## 8. Provas de Soundness
As provas de correção garantem que a lógica de alto nível é fiel à semântica operacional:
- **`step_instr_to_step` (`F_Step_Interp_Sound.lean`)**: Prova que um passo do interpretador corresponde a um passo na relação `step`.
- **`wp_sound` e `vcg_sound` (`H_Ver_Cond_Gen_Sound.lean`)**: Teoremas fundamentais que provam que se as condições geradas pelo VCG forem verdadeiras, então a tríplice de Hoare correspondente é válida.
- **`hoare_step_sound` (`I_Hoare_Step_Sound.lean`)**: Prova que a validade de uma tríplice é preservada através de um passo de execução.
- **`hoare_run_sound` (`J_Run_Sound.lean`)**: Prova que a validade de uma tríplice implica que a pós-condição será satisfeita no final da execução de um programa completo.

---

## 9. Exemplos e Verificação de Programas (`K_Programs.lean`)
Este módulo demonstra a aplicação prática da ferramenta em filtros eBPF reais:
- **`test_add`**: Verificação de somas simples em registradores.
- **`prog_only_arp`**: Um filtro que permite apenas pacotes ARP ($0x0806$), verificando o campo do protocolo no cabeçalho Ethernet.
- **`prog_subnet`**: Verifica se um pacote pertence a uma sub-rede específica através de operações de máscara de bits (`and_K`) e saltos.
- **`prog_only_IPv4_TCP_SSH`**: Um filtro complexo que valida múltiplos campos (EtherType, Protocolo IP e Porta TCP 22), demonstrando o poder do VCG em lidar com lógica de ramificação densa.
