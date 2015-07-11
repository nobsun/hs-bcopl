# hs-bcopl

五十嵐淳：『プログラミング言語の基礎概念』の読書会に参加するにあったって，
予習用に自動導出器をHaskellで書いてみようという試みです．

ここにあるのは今のところ，正しく動く保証はまったくない（残念な）システムです．

### 第1章

- ``Language.BCoPL.Nat.hs``： 自然数の加算・乗算
- ``Language.BCoPL.CompareNat.hs``： 自然数の比較
- ``Language.BCoPL.EvalNatExp.hs``： 算術式の評価
- ``Language.BCoPL.ReduceNatExp.hs``： 算術式の簡約

使用例（出力の改行は編集でいれたもの）

```
% cd src/Language/BCoPL/
% ghci -v0 -i../.. ReduceNatExp.hs
ghci> sessionMulti'
ReduceMulti> S(Z)*S(Z)+S(Z)*S(Z) -*-> S(S(Z))
S(Z) * S(Z) + S(Z) * S(Z) -*-> S(S(Z)) by MR-Multi {
  S(Z) * S(Z) + S(Z) * S(Z) -*-> S(Z) + S(Z) * S(Z) by MR-One {
    S(Z) * S(Z) + S(Z) * S(Z) ---> S(Z) + S(Z) * S(Z) by R-PlusL {
      S(Z) * S(Z) ---> S(Z) by R-Times {
        S(Z) times S(Z) is S(Z) by T-Succ {
          Z times S(Z) is Z by T-Zero {  } ;
          S(Z) plus Z is S(Z) by P-Succ {
            Z plus Z is Z by P-Zero {  }
          }
        }
      }
    }
  } ;
  S(Z) + S(Z) * S(Z) -*-> S(S(Z)) by MR-Multi {
    S(Z) + S(Z) * S(Z) -*-> S(Z) + S(Z) by MR-One {
      S(Z) + S(Z) * S(Z) ---> S(Z) + S(Z) by R-PlusR {
        S(Z) * S(Z) ---> S(Z) by R-Times {
          S(Z) times S(Z) is S(Z) by T-Succ {
            Z times S(Z) is Z by T-Zero {  } ;
            S(Z) plus Z is S(Z) by P-Succ {
              Z plus Z is Z by P-Zero {  }
            }
          }
        }
      }
    } ;
    S(Z) + S(Z) -*-> S(S(Z)) by MR-One {
      S(Z) + S(Z) ---> S(S(Z)) by R-Plus {
        S(Z) plus S(Z) is S(S(Z)) by P-Succ {
          Z plus S(Z) is S(Z) by P-Zero {  }
        }
      }
    }
  }
}
```


