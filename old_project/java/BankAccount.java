public class BankAccount implements IBankAccount {
    private /*@ spec_public @*/ int balance;


    //@ assignable \everything;
    //@ ensures balance == initialBalance;
    public BankAccount(int initialBalance) {
        balance = initialBalance;
    }
    //@ also
    //@ requires amount >= 0 && ((long)getBalance() - (long)amount) >= Integer.MIN_VALUE;
    //@ ensures getBalance() == \old(getBalance()) - amount;
    //@ also
    //@ public exceptional_behavior
    //@ requires amount >= 0 && ((long)getBalance() - (long)amount) < Integer.MIN_VALUE;
    //@ signals_only IllegalArgumentException;
    public void withdraw(int amount) {
        if ((long) balance - (long) amount < Integer.MIN_VALUE) {
        throw new IllegalArgumentException("Withdrawal would cause underflow");
    }
    balance -= amount;
}

    //@ also
    //@ ensures \result == balance;
    public /*@ pure @*/ int getBalance() {
        return balance;
    }
}

