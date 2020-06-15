import React from 'react';
export const ReadOnlyContext = React.createContext(false);

export const FunctionsContext = React.createContext({
	changeText: console.log,
});
