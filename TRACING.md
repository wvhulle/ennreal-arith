# Enhanced Tracing for Cache Debugging

The ENNReal arithmetic tactic system now includes comprehensive tracing capabilities designed to help identify and debug cache-related issues. This document explains how to use the enhanced tracing system.

## Trace Class Organization

The tracing system is organized into logical categories:

### Core Tracing
- `ENNRealArith`: Main trace class for high-level tactic operations
- `ENNRealArith.debug`: General debugging information

### Expression Analysis and Caching
- `ENNRealArith.atom_search`: Expression atom discovery process
- `ENNRealArith.atom_search.cache`: Cache hit/miss detection in atom search
- `ENNRealArith.atom_search.performance`: Performance metrics for atom search

### Expression Conversion and Lifting
- `ENNRealArith.enn_conversion`: ENNReal to Real conversion process
- `ENNRealArith.enn_conversion.cache`: Caching behavior during conversion
- `ENNRealArith.ofreal_lifting`: Operator lifting transformations
- `ENNRealArith.ofreal_lifting.cache`: Cache efficiency in lifting operations
- `ENNRealArith.ofreal_lifting.performance`: Performance metrics for lifting

### Goal State Management
- `ENNRealArith.goal_state`: Goal state snapshots and changes
- `ENNRealArith.goal_transformations`: Detailed goal transformation tracking

### Computation and Fallbacks
- `ENNRealArith.real_computation`: Real arithmetic computation process
- `ENNRealArith.real_computation.cache`: Cache hits in computation strategies
- `ENNRealArith.fallback_strategies`: Fallback strategy execution

### Diagnostics and Performance
- `ENNRealArith.error_handling`: Error conditions and recovery
- `ENNRealArith.performance_metrics`: Execution timing and efficiency metrics

## Usage Examples

### Basic Cache Debugging
To enable basic cache debugging, use:
```lean
set_option trace.ENNRealArith.atom_search.cache true
set_option trace.ENNRealArith.enn_conversion.cache true
set_option trace.ENNRealArith.ofreal_lifting.cache true
```

### Performance Analysis
To analyze performance bottlenecks:
```lean
set_option trace.ENNRealArith.performance_metrics true
set_option trace.ENNRealArith.atom_search.performance true
set_option trace.ENNRealArith.ofreal_lifting.performance true
```

### Comprehensive Debugging
For full debugging information:
```lean
set_option trace.ENNRealArith true
set_option trace.ENNRealArith.atom_search true
set_option trace.ENNRealArith.atom_search.cache true
set_option trace.ENNRealArith.enn_conversion true
set_option trace.ENNRealArith.ofreal_lifting.cache true
set_option trace.ENNRealArith.goal_transformations true
set_option trace.ENNRealArith.error_handling true
```

### Cache Inconsistency Detection
The system includes automatic detection of potential cache inconsistencies:
- Warnings when progress is reported but goal state doesn't change
- Cache hit/miss statistics
- Performance degradation alerts

## Interpreting Trace Output

### Cache Performance Indicators
- `Cache hit: skipping already visited expression` - Efficient cache usage
- `Cache statistics: N unique expressions processed` - Cache utilization metrics
- `WARNING: Goal state unchanged despite reported progress` - Potential cache bug

### Performance Metrics
- Execution times for each phase (atom search, lifting, computation)
- Atom reduction statistics
- Success/failure rates for different strategies

### Error Patterns
- Conversion failures with detailed error messages  
- Fallback strategy activation
- Goal transformation failures

## Common Cache Issues and Debugging

1. **Expression Re-computation**: Look for repeated atom search on same expressions
2. **Inefficient Lifting**: Check for low success rates in operator lifting
3. **Goal State Loops**: Monitor for unchanged goals despite reported progress
4. **Performance Degradation**: Use timing metrics to identify bottlenecks

The enhanced tracing system provides the visibility needed to identify these issues and optimize the caching strategy accordingly.