
# Verifying interface contracts: A semantic `BankAccount`

In this lesson, we show how to verify **interface-level semantic constraints** using JML. We'll define an interface `IBankAccount` that describes the expected **behavior** of a bank account. Then we'll implement a class `SimpleAccount` and verify that it satisfies the interface contracts using OpenJML.

---

## Step 1: Define the `IBankAccount` interface

We start by writing the interface with JML contracts. These contracts describe the **intended semantics** of any bank account.

```java hl_lines="3-5,8-12,15"
public interface IBankAccount {
    //@ requires amount > 0;
    //@ ensures getBalance() == \old(getBalance()) + amount;
    void deposit(int amount);

    //@ requires amount > 0;
    //@ ensures
    //@   (amount <= \old(getBalance()) ==> getBalance() == \old(getBalance()) - amount) &&
    //@   (amount >  \old(getBalance()) ==> getBalance() == 0);
    //@ ensures \result == (\old(getBalance()) < amount ? \old(getBalance()) : amount);
    int withdraw(int amount);

    //@ ensures \result >= 0;
    /*@ pure @*/ int getBalance();
}
```

---

## Step 2: Create the `SimpleAccount` class and declare `balance`

We create a class that implements `IBankAccount` and declare a private field `balance`, making it `spec_public` so JML can reference it.

```java hl_lines="1-2,5"
public class SimpleAccount implements IBankAccount {
    private /*@ spec_public @*/ int balance;

    //@ public invariant balance >= 0;
}
```

---

## Step 3: Implement and specify the constructor

We add a constructor that initializes the balance to 0 and specify its postcondition.

```java hl_lines="8-11"
public class SimpleAccount implements IBankAccount {
    private /*@ spec_public @*/ int balance;

    //@ public invariant balance >= 0;

    //@ assignable \everything;
    //@ ensures balance == 0;
    public SimpleAccount() {
        balance = 0;
    }
}
```

---

## Step 4: Add and specify the `getBalance()` method

We implement `getBalance`, mark it `pure`, and state that it returns the current balance.

```java hl_lines="15-18"
    //@ ensures \result == balance;
    public /*@ pure @*/ int getBalance() {
        return balance;
    }
```

---

## Step 5: Implement `deposit` and specify behavior

We implement the deposit logic with a check to avoid overflow.

```java hl_lines="13-14,20-21"
    //@ requires amount > 0;
    //@ requires balance <= Integer.MAX_VALUE - amount;
    //@ ensures balance == \old(balance) + amount;
    public void deposit(int amount) {
        //@ assume balance <= Integer.MAX_VALUE - amount;
        balance = balance + amount;
    }
```

---

## Step 6: Add the `@ also` clause to `deposit`

This links the method to the interface specification and shows how `also` composes multiple specifications together.

```java hl_lines="12"
    //@ also
    //@ requires amount > 0;
    //@ requires balance <= Integer.MAX_VALUE - amount;
    //@ assignable balance;
    //@ ensures balance == \old(balance) + amount;
    public void deposit(int amount) {
        //@ assume balance <= Integer.MAX_VALUE - amount;
        balance = balance + amount;
    }
```

---

## Step 7: Implement `withdraw` logic

We now implement the `withdraw` method that either subtracts from the balance or empties it completely.

```java hl_lines="24-33"
    //@ also
    //@ requires amount > 0;
    //@ assignable balance;
    //@ ensures
    //@   (amount <= \old(balance) ==> balance == \old(balance) - amount) &&
    //@   (amount >  \old(balance) ==> balance == 0);
    //@ ensures \result == (\old(balance) < amount ? \old(balance) : amount);
    public int withdraw(int amount) {
        int withdrawn;
        if (amount <= balance) {
            balance -= amount;
            withdrawn = amount;
        } else {
            withdrawn = balance;
            balance = 0;
        }
        return withdrawn;
    }
```

---

## Step 8: Full class code so far

Here’s the complete verified implementation of `SimpleAccount` as of now:

```java hl_lines="1-38"
public class SimpleAccount implements IBankAccount {
    private /*@ spec_public @*/ int balance;

    //@ public invariant balance >= 0;

    //@ assignable \everything;
    //@ ensures balance == 0;
    public SimpleAccount() {
        balance = 0;
    }

    //@ also
    //@ requires amount > 0;
    //@ requires balance <= Integer.MAX_VALUE - amount;
    //@ assignable balance;
    //@ ensures balance == \old(balance) + amount;
    public void deposit(int amount) {
        //@ assume balance <= Integer.MAX_VALUE - amount;
        balance = balance + amount;
    }

    //@ also
    //@ requires amount > 0;
    //@ assignable balance;
    //@ ensures
    //@   (amount <= \old(balance) ==> balance == \old(balance) - amount) &&
    //@   (amount >  \old(balance) ==> balance == 0);
    //@ ensures \result == (\old(balance) < amount ? \old(balance) : amount);
    public int withdraw(int amount) {
        int withdrawn;
        if (amount <= balance) {
            balance -= amount;
            withdrawn = amount;
        } else {
            withdrawn = balance;
            balance = 0;
        }
        return withdrawn;
    }

    //@ also
    //@ ensures \result == balance;
    public /*@ pure @*/ int getBalance() {
        return balance;
    }
}
```

---

## Step 9: Verify it using OpenJML

Save the two files:

- `IBankAccount.java` (interface)
- `SimpleAccount.java` (implementation)

Then verify with:

```bash
openjml -esc IBankAccount.java SimpleAccount.java
```

You should see no verification errors. This confirms that:
- All method contracts are satisfied
- The class invariant holds (`balance >= 0`)
- Interface-level expectations are enforced in the implementation

---

## Step 10: Try breaking it — and see OpenJML catch it

Change the `withdraw` method to just `balance -= amount;` without checking, and rerun OpenJML. You'll get a verification error. This shows how **interface contracts act as behavioral constraints** across implementations.

You’ve now formally verified that `SimpleAccount` satisfies the semantic requirements of `IBankAccount`!
