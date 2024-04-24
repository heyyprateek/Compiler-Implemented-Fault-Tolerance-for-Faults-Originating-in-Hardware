# Compiler-Implemented-Fault-Tolerance-for-Faults-Originating-in-Hardware
The objectives involve implementing a code transformation aimed at enhancing system reliability through code replication, utilizing a combination of static and dynamic analysis to verify code properties at runtime, and gaining experience in generating phi-nodes and ensuring the consistency of SSA-form.

**Description:**

Soft errors, caused by transient hardware errors like cosmic ray strikes or thermal fluctuations, can lead to random bit flips and result in incorrect program behavior. As technology advances and transistors become smaller, the occurrence of soft errors is expected to increase, posing a threat to the reliability of computing systems. Soft errors are already observable in cloud environments, affecting hyperscalers.

One approach to mitigate the impact of faults is by replicating code, similar to how redundant engines enhance the reliability of airplanes. Code replication can be automated at the compiler level, reflecting a broader trend in compiler research and industry usage for automated code transformations beyond performance optimization.

In this project, an algorithm has been implemented to enhance fault tolerance for soft errors by replicating code and safeguarding control flow. To prevent soft errors from corrupting data, instructions in the program will be replicated, and intermediate results will be compared to ensure correctness. If any discrepancies are detected, it's assumed that a soft error has occurred, and the program can either gracefully terminate or attempt to recover to a safe state. However, since recovery mechanisms involve more complex transformations, the focus has been on error detection and program termination.

Two types of errors are targeted for detection:
1. Incorrect computation of integer or pointer values.
2. Proper enforcement of control flow.

The implementation will involve techniques to replicate code segments, compare intermediate results, and ensure consistent control flow. Additionally, static and dynamic analysis will be employed to verify the correctness of computations at runtime. The project aims to enhance system reliability in the face of soft errors, contributing to the growing field of fault-tolerant computing.
