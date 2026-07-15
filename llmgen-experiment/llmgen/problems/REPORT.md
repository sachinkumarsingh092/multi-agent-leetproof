# LeetCode Problem Set Report

This report summarizes the 50 LeetCode problems included in the `llmgen/problems` benchmark set, split into a **development set** (15 problems) and an **evaluation set** (35 problems).

## Summary

| | Total | Easy | Medium | Hard |
|-|-------|------|--------|------|
| Development Set | 15 | 3 | 12 | 0 |
| Evaluation Set | 35 | 25 | 10 | 0 |
| **All** | **50** | **28** | **22** | **0** |

---

## Development Set (15 problems)

| # | Title | Difficulty | Tags |
|---|-------|------------|------|
| 11 | Container With Most Water | Medium | Array, Two Pointers, Greedy |
| 56 | Merge Intervals | Medium | Array, Sorting |
| 57 | Insert Interval | Medium | Array |
| 88 | Merge Sorted Array | Easy | Array, Two Pointers, Sorting |
| 167 | Two Sum II - Input Array Is Sorted | Medium | Array, Two Pointers, Binary Search |
| 204 | Count Primes | Medium | Array, Math, Enumeration, Number Theory |
| 283 | Move Zeroes | Easy | Array, Two Pointers |
| 567 | Permutation in String | Medium | Hash Table, Two Pointers, String, Sliding Window |
| 763 | Partition Labels | Medium | Hash Table, Two Pointers, String, Greedy |
| 912 | Sort an Array | Medium | Array, Divide and Conquer, Sorting, Heap (Priority Queue), Merge Sort, Bucket Sort, Radix Sort, Counting Sort |
| 962 | Maximum Width Ramp | Medium | Array, Two Pointers, Stack, Monotonic Stack |
| 986 | Interval List Intersections | Medium | Array, Two Pointers, Sweep Line |
| 1089 | Duplicate Zeros | Easy | Array, Two Pointers |
| 1574 | Shortest Subarray to be Removed to Make Array Sorted | Medium | Array, Two Pointers, Binary Search, Stack, Monotonic Stack |
| 2161 | Partition Array According to Given Pivot | Medium | Array, Two Pointers, Simulation |

### Development Set — by Tag

| Tag | Problems |
|-----|----------|
| Array | 11, 56, 57, 88, 167, 204, 283, 912, 962, 986, 1089, 1574, 2161 |
| Two Pointers | 11, 88, 167, 283, 567, 763, 962, 986, 1089, 1574, 2161 |
| Sorting | 56, 88, 912 |
| Hash Table | 567, 763 |
| String | 567, 763 |
| Binary Search | 167, 1574 |
| Stack | 962, 1574 |
| Monotonic Stack | 962, 1574 |
| Greedy | 11, 763 |
| Divide and Conquer | 912 |
| Math | 204 |
| Enumeration | 204 |
| Number Theory | 204 |
| Sliding Window | 567 |
| Sweep Line | 986 |
| Prefix Sum | 986 (via Sweep Line / interval) |
| Heap (Priority Queue) | 912 |
| Merge Sort | 912 |
| Bucket Sort | 912 |
| Radix Sort | 912 |
| Counting Sort | 912 |
| Simulation | 2161 |

---

## Evaluation Set (35 problems)

| # | Title | Difficulty | Tags |
|---|-------|------------|------|
| 26 | Remove Duplicates from Sorted Array | Easy | Array, Two Pointers |
| 33 | Search in Rotated Sorted Array | Medium | Array, Binary Search |
| 50 | Pow(x, n) | Medium | Math, Recursion |
| 53 | Maximum Subarray | Medium | Array, Divide and Conquer, Dynamic Programming |
| 75 | Sort Colors | Medium | Array, Two Pointers, Sorting |
| 80 | Remove Duplicates from Sorted Array II | Medium | Array, Two Pointers |
| 121 | Best Time to Buy and Sell Stock | Easy | Array, Dynamic Programming |
| 136 | Single Number | Easy | Array, Bit Manipulation |
| 169 | Majority Element | Easy | Array, Hash Table, Divide and Conquer, Sorting, Counting |
| 191 | Number of 1 Bits | Easy | Divide and Conquer, Bit Manipulation |
| 205 | Isomorphic Strings | Easy | Hash Table, String |
| 217 | Contains Duplicate | Easy | Array, Hash Table, Sorting |
| 238 | Product of Array Except Self | Medium | Array, Prefix Sum |
| 338 | Counting Bits | Easy | Dynamic Programming, Bit Manipulation |
| 383 | Ransom Note | Easy | Hash Table, String, Counting |
| 387 | First Unique Character in a String | Easy | Hash Table, String, Queue, Counting |
| 392 | Is Subsequence | Easy | Two Pointers, String, Dynamic Programming |
| 409 | Longest Palindrome | Easy | Hash Table, String, Greedy |
| 459 | Repeated Substring Pattern | Easy | String, String Matching |
| 496 | Next Greater Element I | Easy | Array, Hash Table, Stack, Monotonic Stack |
| 645 | Set Mismatch | Easy | Array, Hash Table, Bit Manipulation, Sorting |
| 674 | Longest Continuous Increasing Subsequence | Easy | Array |
| 724 | Find Pivot Index | Easy | Array, Prefix Sum |
| 896 | Monotonic Array | Easy | Array |
| 917 | Reverse Only Letters | Easy | Two Pointers, String |
| 918 | Maximum Sum Circular Subarray | Medium | Array, Divide and Conquer, Dynamic Programming, Queue, Monotonic Queue |
| 925 | Long Pressed Name | Easy | Two Pointers, String |
| 1189 | Maximum Number of Balloons | Easy | Hash Table, String, Counting |
| 1207 | Unique Number of Occurrences | Easy | Array, Hash Table |
| 1310 | XOR Queries of a Subarray | Medium | Array, Bit Manipulation, Prefix Sum |
| 1351 | Count Negative Numbers in a Sorted Matrix | Easy | Array, Binary Search, Matrix |
| 1539 | Kth Missing Positive Number | Easy | Array, Binary Search |
| 1552 | Magnetic Force Between Two Balls | Medium | Array, Binary Search, Sorting |
| 1752 | Check if Array Is Sorted and Rotated | Easy | Array |
| 2149 | Rearrange Array Elements by Sign | Medium | Array, Two Pointers, Simulation |

### Evaluation Set — by Tag

| Tag | Problems |
|-----|----------|
| Array | 26, 33, 53, 75, 80, 121, 136, 169, 217, 238, 496, 645, 674, 724, 896, 918, 1207, 1310, 1351, 1539, 1552, 1752, 2149 |
| Two Pointers | 26, 75, 80, 392, 917, 925, 2149 |
| Hash Table | 169, 205, 217, 383, 387, 409, 496, 645, 1189, 1207 |
| String | 205, 383, 387, 392, 409, 459, 917, 925, 1189 |
| Sorting | 75, 169, 217, 645, 1552 |
| Dynamic Programming | 53, 121, 338, 392, 918 |
| Bit Manipulation | 136, 191, 338, 645, 1310 |
| Binary Search | 33, 1351, 1539, 1552 |
| Divide and Conquer | 53, 169, 191, 918 |
| Counting | 169, 383, 387, 1189 |
| Prefix Sum | 238, 724, 1310 |
| Stack | 496 |
| Monotonic Stack | 496 |
| Greedy | 409 |
| Queue | 387, 918 |
| Monotonic Queue | 918 |
| String Matching | 459 |
| Recursion | 50 |
| Math | 50 |
| Matrix | 1351 |
| Simulation | 2149 |

---

## Tag Distribution

### Development Set

| Tag | Count |
|-----|-------|
| Array | 13 |
| Two Pointers | 11 |
| Sorting | 3 |
| Hash Table | 2 |
| String | 2 |
| Binary Search | 2 |
| Stack | 2 |
| Monotonic Stack | 2 |
| Greedy | 2 |
| Divide and Conquer | 1 |
| Math | 1 |
| Enumeration | 1 |
| Number Theory | 1 |
| Prefix Sum | 1 |
| Sliding Window | 1 |
| Sweep Line | 1 |
| Simulation | 1 |
| Heap (Priority Queue) | 1 |
| Merge Sort | 1 |
| Bucket Sort | 1 |
| Radix Sort | 1 |
| Counting Sort | 1 |

### Evaluation Set

| Tag | Count |
|-----|-------|
| Array | 23 |
| Hash Table | 10 |
| Two Pointers | 7 |
| String | 9 |
| Sorting | 5 |
| Dynamic Programming | 5 |
| Bit Manipulation | 5 |
| Divide and Conquer | 4 |
| Counting | 4 |
| Binary Search | 4 |
| Prefix Sum | 3 |
| Queue | 2 |
| Math | 1 |
| Recursion | 1 |
| Stack | 1 |
| Monotonic Stack | 1 |
| Monotonic Queue | 1 |
| Greedy | 1 |
| String Matching | 1 |
| Matrix | 1 |
| Simulation | 1 |
