# Troubleshooting Guide

This section outlines common problems you might encounter while completing the tasks, along with possible causes and suggested fixes.

---

## Problem: Dropdown list not appearing
**Possible causes:**
- Data validation not applied to the correct column
- Column was selected after entering values

**Fix:**
- Select the column again
- Go to `Data > Data validation`
- Make sure "List of items" is selected and the values are entered correctly

---

## Problem: "#REF!" error in `IMPORTRANGE`
**Possible causes:**
- Access not granted to the source sheet
- Sheet name or range is incorrect

**Fix:**
- Paste the `IMPORTRANGE` formula alone in any blank cell
- Click “Allow access” when prompted
- Double-check the sheet name and range (e.g. `Sheet1!A2:D`)

---

## Problem: Pie chart shows wrong categories
**Possible causes:**
- Label and data ranges are mismatched
- Empty or inconsistent category cells

**Fix:**
- Check that your label range (e.g. `C2:C`) matches your data range (e.g. `D2:D`)
- Remove any blank or misspelled categories

---

## Problem: Conditional formatting highlights everything
**Possible causes:**
- Formula applies to the wrong range
- Row references include the header

**Fix:**
- Make sure the formatting range starts from row 2, not row 1
- Check that your formula uses relative references (e.g., `B2` not `B$2`)

---

## Problem: Circular dependency error
**Possible causes:**
- You entered a formula in a cell that’s part of the formula’s own output range

**Fix:**
- Move the formula to a cell outside the table it’s operating on
- Avoid pasting formulas into the middle of dynamic data blocks

---

## Problem: Only one import shows in merged table
**Possible causes:**
- One of the `IMPORTRANGE` calls has a silent error
- The stacking formula is inside an area it tries to overwrite

**Fix:**
- Test each `IMPORTRANGE` formula individually first
- Place the `QUERY` formula far below the imported ranges to avoid overlap

---

## Problem: Filter not working as expected
**Possible causes:**
- Filter column contains inconsistent or misspelled values

**Fix:**
- Check for extra spaces or typos in the "Status" or "Category" columns
- Use the dropdowns created with data validation to enforce consistency

