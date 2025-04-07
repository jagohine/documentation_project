
public interface IBankAccount {
    //@ requires amount >= 0 && ((long)getBalance() - (long)amount) >= Integer.MIN_VALUE;
    //@ ensures getBalance() == \old(getBalance()) - amount;
    //@ also
    //@ public exceptional_behavior
    //@ requires amount >= 0 && ((long)getBalance() - (long)amount) < Integer.MIN_VALUE;
    //@ signals_only IllegalArgumentException;
    void withdraw(int amount);

    //@ ensures \result >= Integer.MIN_VALUE;
    /*@ pure @*/ int getBalance();
}
