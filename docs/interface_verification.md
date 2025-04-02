
# Task 3: Specify and verify the correctness of an interface implementation (with JML)

In this task, we will specify and verify the correctness of a Java class that implements an interface, using JML. We'll define the interface and implementation in plain Java first, then progressively add JML specifications. Our goal is to ensure that the implementation respects the contracts declared in the interface.

Each step includes the complete code so far, with new lines **highlighted**.

---

## Step 1: Define the interface

We begin by defining a banking interface with three methods: `deposit`, `withdraw`, and `getBalance`. This interface is intentionally underspecified at this stage.

```java
public interface IBankAccount {
    void deposit(int amount);
    void withdraw(int amount);
    int getBalance();
}
```

---

## Step 2: Implement the interface

Next, we define a concrete implementation, `SimpleAccount`, which maintains a private balance field. The logic enforces basic constraints (no overdrafts or negative transactions) using Java exceptions.

```java
public class SimpleAccount implements IBankAccount {
    private int balance;

    public SimpleAccount() {
        this.balance = 0;
    }

    public void deposit(int amount) {
        if (amount < 0) {
            throw new IllegalArgumentException("amount must be non-negative");
        }
        if (amount > Integer.MAX_VALUE - balance) {
            throw new IllegalArgumentException("deposit would cause overflow");
        }
        balance += amount;
    }

    public void withdraw(int amount) {
        if (amount < 0) {
            throw new IllegalArgumentException("amount must be non-negative");
        }
        if (amount > balance) {
            throw new IllegalArgumentException("insufficient funds");
        }
        balance -= amount;
    }

    public int getBalance() {
        return balance;
    }
}
```

**Why?** We want our implementation to enforce safety at runtime, which we’ll later formalize and verify with JML.

---

## Step 3: Mark `getBalance()` as pure in the interface

To use `getBalance()` in specifications, we must mark it as `pure`. In JML, a method is *pure* if it has no side effects and may be called in annotations.

```java
public interface IBankAccount {
    void deposit(int amount);
    void withdraw(int amount);

    /*@ pure @*/
    int getBalance();
}
```

**Why?** This makes `getBalance()` usable in JML expressions like `requires`, `ensures`, and `invariant`.

---

## Step 4: Add `ensures` clause to `deposit()` in the interface

We now specify what `deposit` is supposed to do: if you deposit a non-negative amount, the balance should increase accordingly.

```java
public interface IBankAccount {
    /*@ requires amount >= 0;
      @ ensures getBalance() == \old(getBalance()) + amount;
      @ also
      @ requires amount < 0;
      @ signals (IllegalArgumentException e) true;
      @*/
    void deposit(int amount);

    void withdraw(int amount);

    /*@ pure @*/
    int getBalance();
}
```

**Why?** This expresses both the normal postcondition and the behavior when invalid input is given.

---

## Step 5: Add `withdraw()` specification to the interface

Now we specify that withdrawals must be non-negative and not exceed the balance, or else an exception is thrown.

```java
public interface IBankAccount {
    /*@ requires amount >= 0;
      @ ensures getBalance() == \old(getBalance()) + amount;
      @ also
      @ requires amount < 0;
      @ signals (IllegalArgumentException e) true;
      @*/
    void deposit(int amount);

    /*@ requires amount >= 0 && amount <= getBalance();
      @ ensures getBalance() == \old(getBalance()) - amount;
      @ also
      @ requires amount < 0 || amount > getBalance();
      @ signals (IllegalArgumentException e) true;
      @*/
    void withdraw(int amount);

    /*@ pure @*/
    int getBalance();
}
```

**Why?** This ensures the caller knows under which conditions `withdraw` will succeed or fail.

---

## Step 6: Add model field and `represents` clause to implementation

We introduce a `model` field that represents the abstract value of the object, and a `represents` clause to link it to the internal `balance`.

```java
public class SimpleAccount implements IBankAccount {
    private int balance;

    /*@ public model int abstractBalance;
      @ represents abstractBalance <- balance;
      @*/

    public SimpleAccount() {
        this.balance = 0;
    }

    public void deposit(int amount) {
        if (amount < 0) {
            throw new IllegalArgumentException("amount must be non-negative");
        }
        if (amount > Integer.MAX_VALUE - balance) {
            throw new IllegalArgumentException("deposit would cause overflow");
        }
        balance += amount;
    }

    public void withdraw(int amount) {
        if (amount < 0) {
            throw new IllegalArgumentException("amount must be non-negative");
        }
        if (amount > balance) {
            throw new IllegalArgumentException("insufficient funds");
        }
        balance -= amount;
    }

    public int getBalance() {
        return balance;
    }
}
```

**Why?** This allows us to write specifications in terms of a clean abstract value (`abstractBalance`) while hiding implementation details.

---

## Step 7–10: Specification of getBalance, deposit, withdraw, and verification

[... content was truncated for brevity here. See the next step for file write.]
