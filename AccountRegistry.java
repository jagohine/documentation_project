public class AccountRegistry {
    private /*@ spec_public @*/ int[] accountIDs;
    private /*@ spec_public @*/ int size;

    //@ public invariant 0 <= size && size <= accountIDs.length;
    //@ public invariant (\forall int i; 0 <= i && i < size;
    //@     (\forall int j; 0 <= j && j < size && i != j;
    //@         accountIDs[i] != accountIDs[j]));

    //@ assignable \everything;
    //@ ensures size == 0;
    //@ ensures accountIDs.length == 100;
    public AccountRegistry() {
        accountIDs = new int[100];
        size = 0;
    }

    /*@ assignable accountIDs[*], size; // Use accountIDs[*] for safety
    @ ensures (\old(contains(id)) || \old(isFull())) ==>
    @      size == \old(size); // If already present or full, size doesn't change
    @ ensures (!\old(contains(id)) && !\old(isFull())) ==>
    @      size == \old(size) + 1        // If added, size increases
    @   && accountIDs[\old(size)] == id; // and ID is at the new last position
    @*/
    public void addAccount(int id) {
        if (size < accountIDs.length && !contains(id)) {
            accountIDs[size] = id;
            size++;
        }
    }

    //@ ensures \result <==> (\exists int k; 0 <= k && k < size; accountIDs[k] == id);
    public /*@ pure @*/ boolean contains(int id) {
        //@ loop_invariant 0 <= i && i <= size;
        //@ loop_invariant (\forall int j; 0 <= j && j < i; accountIDs[j] != id);
        //@ decreases size - i;
        for (int i = 0; i < size; i++) {
            if (accountIDs[i] == id) return true;
        }
        return false;
    }

    //@ ensures \result <==> size == accountIDs.length;
    public /*@ pure @*/ boolean isFull() {
        return size == accountIDs.length;
    }

    
}
