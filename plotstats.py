import json
import pandas as pd
import matplotlib.pyplot as plt
import numpy as np

# Load the JSON data from file
with open('stats.json') as f:
    data = json.load(f)

# Convert the data into a pandas DataFrame
df = pd.DataFrame(data)

# Create a scatter plot with logarithmic axes
plt.figure(figsize=(8, 6))
plt.scatter(df['kernelTime'], df['lazyWhnfTime'], color='blue')

# Add a straight line where lazyWhnfTime equals kernelTime (y = x)
plt.plot([1000, max(df['kernelTime'].max(), df['lazyWhnfTime'].max())],
         [1000, max(df['kernelTime'].max(), df['lazyWhnfTime'].max())],
         'r--', label='y = x')

# Set logarithmic scale for both axes
plt.xscale('log')
plt.yscale('log')

# Add labels and title
plt.xlabel('Kernel Time (ns)')
plt.ylabel('Lazy WHNF Time (ns)')
plt.title('Scatter Plot of Lazy WHNF Time vs Kernel Time (Log-Log Scale)')

print(df['kernelTime'].sum(), df['lazyWhnfTime'].sum())

# Show the plot
plt.show()

