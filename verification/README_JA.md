# momo の依存実現核 — 研究案と機械検査範囲

2026-09-20。作業名であり、完成した新型理論や新規性の確立を宣言する名称ではない。

## この成果の位置付け

ローカルの実行環境は TransportTimeoutError で動作せず、検査は GitHub Actions の隔離された検証ブランチで実施した。ローカルの Lean 実行成功とは報告しない。正常系ソースを Lean 4.33.0 で検査し、実際の公理依存と、わざと壊した規則の失敗ログを成果物に残す。最終状態は同梱の status.txt と verification.log で確認する。

これは **高階・並行・非停止の実行機械と、その同じ機械上の依存実現の意味論的断片** である。独立した宇宙階層・帰納型・構文的型検査器を備えた完成済みの言語ではない。

## 根本原理

型の意味を、論理的な値 a と実際の値 v の関係 A(a,v) として与える。数学的な記述を増やしても、実体は増えない。資源を二つ返すなら、実際の二つの出力と、それを作る許された実行が必要になる。

論理的なデータと実体を混同しないため、次を区別する。

- overlay: 一つの v が二つの依存した説明を満たす。実体を複製しない。
- tensor: 二つの実体 x,y を組にし、所有資源が互いに素であることを要求する。
- erasedAll: 全ての論理的添字について **同じ v** が仕様を満たす。
- erasedExists: 論理的な証人は保持するが、実行値にその証人を復元しない。
- pi: 捕獲環境を実行値の内部に隠した依存関数。全ての適切な引数について、同じ本文の全実行が契約を満たす。

これらは全て同じ View 構造の具体的な定義であり、独立した外部モデルの存在を仮定しない。ただし、それらが独立した全構文的型理論のモデルになることまで本成果で証明したわけではない。論理部分のホストは Lean である。

## Good と停止の意味

Good p x Q は次の三条件を同時に要求する。

1. 初期状態からの遷移が整礎であること (Acc Before)。都合のよい一つの終了実行の存在だけではない。
2. 各到達状態が返値であるか、次の遷移を持つこと。単に停止した不正状態では契約を満たさない。
3. 全ての終了実行について、その同じ返値・履歴が Q を満たすこと。

並行実行では、異なる性質を満たす別々の実行を一つの成功へ混ぜてはならない。same_run_intersection は同じプログラムの全返値に対する二つの性質を結合する。

repeat による永続 Task は機械に含むが、全ての Task が Good を満たすとはしない。永続 Task の資源保存は、終了を仮定せず、全有限実行接頭辞に対して証明する。公平性や外部機器の応答性は保証していない。

## 実行機械

ResourcePrefix.lean は以下を独立した構文と小ステップ規則として定義する。

- Code: 恒等、逐次、並置、閉包生成、適用、自然数リテラル・加算・複製、資源解放、出力、永続反復。
- Val: unit、自然数、識別子付き資源、ペア、本文と捕獲環境を持つ閉包。
- Task: 返値、実行中のコード、逐次継続、並行中の二つの Task。
- Step: 左右どちらの Task も一歩動けるインターリーブ意味論。
- Prefix: 有限個の実際の Step の列。固定の燃料制限ではない。

資源 k の個数 mass(k,s) は、返値だけでなく、実行中の Task と閉包環境を走査する。spent(k,trace) は明示的な解放イベントの個数である。

中心定理は

    Prefix s events t
      → mass(k,s) = mass(k,t) + spent(k,events)

である。一歩の保存は具体的な Step の全構築子から導き、保存則自体を Step の前提に入れていない。そのため所有権の条件を満たさない生プログラムが行き詰まることはあり得るが、途中で勝手に所有資源が複製されたり消えたりする成功ステップは存在しない。

## 証明群

ResourcePrefix.lean:

- step_balance / prefix_balance: 各ステップ・全有限接頭辞で資源収支が一致。
- unique_at_every_prefix: 初期状態で資源が重複しなければ各到達状態でも重複しない。
- no_double_release: 有効な初期状態から同じ資源を二重解放しない。
- no_token_copy: 一つの資源を同じ資源二つへ変える実行列はない。
- no_uniform_bit: 一つの返値関係の全返値が、消去された任意の Bool に合わせて 0 と 1 の両方になることはない。返値関係の非空性は明示的前提。

Examples.lean:

- owned_call: 実際に閉包へ捕獲した資源が適用後に返される。
- both_orders: 二つの並行出力について、両方の順序の実行が存在する。
- repeat_prefix: 任意回数の反復に対応する接頭辞を構成する。有限上限付きテストではない。

DependentRealization.lean:

- primitive_good: 一歩の実行を完全に特徴付けた原始処理は total な契約を満たす。
- dependent_curry: 捕獲値と引数の両方に依存する結果型を保った閉包の構成。
- dependent_apply: 表現された関数を適切な分離された入力に適用すると Good が成立。
- eliminate_erased: 一つのコードが全添字について契約を満たす場合の消去済み存在証人の除去。
- same_run_intersection: 同じ実行の全返値について性質を結合。
- identity_refine: 同じ値を説明する証拠の追加は恒等コードで実現できる。
- owned_closure_total: 実際に一つの資源を捕獲し、入力した自然数とその資源を返す依存関数の非空の具体例。

## 負の検査

check_mutations.py は Step に次の規則をそれぞれ追加する。

- 資源一つを同じ識別子の資源二つへ無償で変える。
- 資源を消すが解放イベントを出さない。

それぞれが step_balance の証明中で失敗することを検査する。mutations/ 内の Lean ファイルは **意図的に失敗するソース** であり、正常系の証明と混同しない。

## 公理と信頼境界

正常系の証明で sorry、admit、独自 axiom、unsafe、native_decide は使用しない。公理依存は #print axioms の実出力を参照する。基礎の算術証明は propext と Quot.sound に依存する。『無公理の新しい論理を実装した』という主張ではない。

Lean、配布物の真正性、実行したホスト・CI環境は信頼境界に残る。コードや証明自体の検査と、実機や全コンパイラの検証は別である。

## 再検査

Lean 4.33.0 と Python 3 を用意し、このディレクトリで実行する。mathlib や lake build は不要。

```sh
set -euo pipefail
export LEAN_PATH="$PWD"
lean --version
lean -o ResourcePrefix.olean ResourcePrefix.lean
lean -o Examples.olean Examples.lean
lean -o DependentRealization.olean DependentRealization.lean
python3 check_mutations.py "$(command -v lean)"
```

CI は以前取得した期限付きツールチェーン artifact を参照するため、その artifact の期限後に同じ CI を再実行するには、同じ版のツールチェーンを再取得する必要がある。上記のローカル検査手順はその artifact に依存しない。

## 今回確立していないこと

- 世界初であること、または既存理論より普遍的に小さいこと。
- 独立した依存型検査器、宇宙階層、一般の相互・入れ子・依存帰納、全構文の代入と型保存。
- Lean 全数学の翻訳、独立した無矛盾性証明・一般の強正規化。
- 一般のソース項の実消去、最適化・ネイティブコンパイラの正しさ。
- 動的な割当て、借用、共有ヒープ、実機のメモリモデル、デッドロック不在・公平性・レイテンシ。

特に「資源が突然消えない」は「必ずいつか資源を解放する」ではない。反復中に資源を保持し続けることは許される。

## 新規性の候補と先行研究

依存交差、消去、線形な実現関係、依存した閉包変換には直接的な先行研究がある。

- Cedille: https://cedille.github.io/cedille/html/about.html
- Typed Closure Conversion for the Calculus of Constructions: https://arxiv.org/abs/1808.04006
- Interaction Trees: https://arxiv.org/abs/1906.00046
- Type Theory With Erasure: https://arxiv.org/abs/2605.00655
- Impredicativity in Linear Dependent Type Theory: https://arxiv.org/abs/2602.08846

候補として評価するのは、数学的な説明を重ねることと、実体を分離・移送することを区別し、全てを一つの資源保存機械へ結び付ける設計である。今回の証明は、この限定した構成が矛盾した成功例に依存せず機能することを裏付ける。新理論としての優位性を証明するものではない。
