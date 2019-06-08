# TLA+

TLA+ has been described as exhaustively-testable pseudocode, and is an initialism for Temporal Logic of Actions, per [wikipedia](https://en.wikipedia.org/wiki/TLA%2B)

### Getting started

1. Grab the [latest release](https://github.com/tlaplus/tlaplus/releases/latest) of TLA Toolbox (for your OS)
2. Check out the various user manuals and guides that the toolbox comes with under the Help menu.
	- [user guide](http://127.0.0.1:60003/help/index.jsp?topic=%2Forg.lamport.tla.toolbox.doc%2Fhtml%2Fgettingstarted%2Fgettingstarted.html)
	- Help > TLA+ Cheat Sheet
	- Help > PlusCal User Manual 
3. Check out the examples on learntla.com. E.g., [this one](https://learntla.com/introduction/example/)

### PlusCal

The given example is in PlusCal, which is a higher level pseudocode language that gets transpiled into TLA+.   

examples/transfer.tla
```
---- MODULE transfer ----
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10, money \in 1..11;

begin
A: alice_account := alice_account - money;
B: bob_account := bob_account + money;
C: assert alice_account >= 0;

end algorithm *)
====
```

- Hitting `⌘T` on mac translates this PlusCal to TLA+. 
- Create a new "model" (name it TransferModel).
- Run TLC on the model.
- This immediately fails, since our test case included `money=11` which violates our invariant `assert alic_account >= 0`
- Profit!


### References
- [The TLA+ Hyperbook](http://lamport.azurewebsites.net/tla/hyperbook.html)
- [Hillel Wayne's website](https://learntla.com/)
- [Practical TLA+](https://www.apress.com/us/book/9781484238288)
